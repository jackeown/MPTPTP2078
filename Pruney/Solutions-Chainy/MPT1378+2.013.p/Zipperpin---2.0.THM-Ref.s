%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DcIoKrO4ZT

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:47 EST 2020

% Result     : Theorem 5.19s
% Output     : Refutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 174 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  826 (2531 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
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

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('15',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X7 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('44',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ X19 @ ( k1_tops_1 @ X20 @ X21 ) )
      | ( m1_connsp_2 @ X21 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['61','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DcIoKrO4ZT
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.19/5.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.19/5.41  % Solved by: fo/fo7.sh
% 5.19/5.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.19/5.41  % done 7870 iterations in 4.952s
% 5.19/5.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.19/5.41  % SZS output start Refutation
% 5.19/5.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.19/5.41  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 5.19/5.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.19/5.41  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.19/5.41  thf(sk_A_type, type, sk_A: $i).
% 5.19/5.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.19/5.41  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.19/5.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.19/5.41  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 5.19/5.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.19/5.41  thf(sk_D_1_type, type, sk_D_1: $i).
% 5.19/5.41  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.19/5.41  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.19/5.41  thf(sk_B_type, type, sk_B: $i).
% 5.19/5.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.19/5.41  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.19/5.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.19/5.41  thf(t3_connsp_2, conjecture,
% 5.19/5.41    (![A:$i]:
% 5.19/5.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.19/5.41       ( ![B:$i]:
% 5.19/5.41         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.19/5.41           ( ![C:$i]:
% 5.19/5.41             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.19/5.41               ( ![D:$i]:
% 5.19/5.41                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.19/5.41                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 5.19/5.41                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 5.19/5.41                     ( m1_connsp_2 @
% 5.19/5.41                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 5.19/5.41  thf(zf_stmt_0, negated_conjecture,
% 5.19/5.41    (~( ![A:$i]:
% 5.19/5.41        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.19/5.41            ( l1_pre_topc @ A ) ) =>
% 5.19/5.41          ( ![B:$i]:
% 5.19/5.41            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.19/5.41              ( ![C:$i]:
% 5.19/5.41                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.19/5.41                  ( ![D:$i]:
% 5.19/5.41                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.19/5.41                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 5.19/5.41                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 5.19/5.41                        ( m1_connsp_2 @
% 5.19/5.41                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 5.19/5.41    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 5.19/5.41  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('1', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('2', plain,
% 5.19/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf(d1_connsp_2, axiom,
% 5.19/5.41    (![A:$i]:
% 5.19/5.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.19/5.41       ( ![B:$i]:
% 5.19/5.41         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.19/5.41           ( ![C:$i]:
% 5.19/5.41             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.19/5.41               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 5.19/5.41                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 5.19/5.41  thf('3', plain,
% 5.19/5.41      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.19/5.41         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 5.19/5.41          | ~ (m1_connsp_2 @ X21 @ X20 @ X19)
% 5.19/5.41          | (r2_hidden @ X19 @ (k1_tops_1 @ X20 @ X21))
% 5.19/5.41          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 5.19/5.41          | ~ (l1_pre_topc @ X20)
% 5.19/5.41          | ~ (v2_pre_topc @ X20)
% 5.19/5.41          | (v2_struct_0 @ X20))),
% 5.19/5.41      inference('cnf', [status(esa)], [d1_connsp_2])).
% 5.19/5.41  thf('4', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((v2_struct_0 @ sk_A)
% 5.19/5.41          | ~ (v2_pre_topc @ sk_A)
% 5.19/5.41          | ~ (l1_pre_topc @ sk_A)
% 5.19/5.41          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 5.19/5.41          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 5.19/5.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['2', '3'])).
% 5.19/5.41  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('7', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((v2_struct_0 @ sk_A)
% 5.19/5.41          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 5.19/5.41          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 5.19/5.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('demod', [status(thm)], ['4', '5', '6'])).
% 5.19/5.41  thf('8', plain,
% 5.19/5.41      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.19/5.41        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 5.19/5.41        | (v2_struct_0 @ sk_A))),
% 5.19/5.41      inference('sup-', [status(thm)], ['1', '7'])).
% 5.19/5.41  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('10', plain,
% 5.19/5.41      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 5.19/5.41      inference('demod', [status(thm)], ['8', '9'])).
% 5.19/5.41  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 5.19/5.41      inference('clc', [status(thm)], ['10', '11'])).
% 5.19/5.41  thf(d3_tarski, axiom,
% 5.19/5.41    (![A:$i,B:$i]:
% 5.19/5.41     ( ( r1_tarski @ A @ B ) <=>
% 5.19/5.41       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.19/5.41  thf('13', plain,
% 5.19/5.41      (![X1 : $i, X3 : $i]:
% 5.19/5.41         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_tarski])).
% 5.19/5.41  thf(d3_xboole_0, axiom,
% 5.19/5.41    (![A:$i,B:$i,C:$i]:
% 5.19/5.41     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 5.19/5.41       ( ![D:$i]:
% 5.19/5.41         ( ( r2_hidden @ D @ C ) <=>
% 5.19/5.41           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.19/5.41  thf('14', plain,
% 5.19/5.41      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.19/5.41         (~ (r2_hidden @ X8 @ X6)
% 5.19/5.41          | (r2_hidden @ X8 @ X7)
% 5.19/5.41          | (r2_hidden @ X8 @ X5)
% 5.19/5.41          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.19/5.41  thf('15', plain,
% 5.19/5.41      (![X5 : $i, X7 : $i, X8 : $i]:
% 5.19/5.41         ((r2_hidden @ X8 @ X5)
% 5.19/5.41          | (r2_hidden @ X8 @ X7)
% 5.19/5.41          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 5.19/5.41      inference('simplify', [status(thm)], ['14'])).
% 5.19/5.41  thf('16', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 5.19/5.41          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 5.19/5.41          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['13', '15'])).
% 5.19/5.41  thf('17', plain,
% 5.19/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf(t3_subset, axiom,
% 5.19/5.41    (![A:$i,B:$i]:
% 5.19/5.41     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.19/5.41  thf('18', plain,
% 5.19/5.41      (![X13 : $i, X14 : $i]:
% 5.19/5.41         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 5.19/5.41      inference('cnf', [status(esa)], [t3_subset])).
% 5.19/5.41  thf('19', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 5.19/5.41      inference('sup-', [status(thm)], ['17', '18'])).
% 5.19/5.41  thf('20', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         (~ (r2_hidden @ X0 @ X1)
% 5.19/5.41          | (r2_hidden @ X0 @ X2)
% 5.19/5.41          | ~ (r1_tarski @ X1 @ X2))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_tarski])).
% 5.19/5.41  thf('21', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 5.19/5.41      inference('sup-', [status(thm)], ['19', '20'])).
% 5.19/5.41  thf('22', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]:
% 5.19/5.41         ((r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_C_1 @ X0)) @ X0)
% 5.19/5.41          | (r1_tarski @ (k2_xboole_0 @ sk_C_1 @ X0) @ X1)
% 5.19/5.41          | (r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_C_1 @ X0)) @ 
% 5.19/5.41             (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['16', '21'])).
% 5.19/5.41  thf('23', plain,
% 5.19/5.41      (![X1 : $i, X3 : $i]:
% 5.19/5.41         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_tarski])).
% 5.19/5.41  thf('24', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A))
% 5.19/5.41          | (r2_hidden @ 
% 5.19/5.41             (sk_C @ (u1_struct_0 @ sk_A) @ (k2_xboole_0 @ sk_C_1 @ X0)) @ X0)
% 5.19/5.41          | (r1_tarski @ (k2_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['22', '23'])).
% 5.19/5.41  thf('25', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((r2_hidden @ 
% 5.19/5.41           (sk_C @ (u1_struct_0 @ sk_A) @ (k2_xboole_0 @ sk_C_1 @ X0)) @ X0)
% 5.19/5.41          | (r1_tarski @ (k2_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('simplify', [status(thm)], ['24'])).
% 5.19/5.41  thf('26', plain,
% 5.19/5.41      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('27', plain,
% 5.19/5.41      (![X13 : $i, X14 : $i]:
% 5.19/5.41         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 5.19/5.41      inference('cnf', [status(esa)], [t3_subset])).
% 5.19/5.41  thf('28', plain, ((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 5.19/5.41      inference('sup-', [status(thm)], ['26', '27'])).
% 5.19/5.41  thf('29', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         (~ (r2_hidden @ X0 @ X1)
% 5.19/5.41          | (r2_hidden @ X0 @ X2)
% 5.19/5.41          | ~ (r1_tarski @ X1 @ X2))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_tarski])).
% 5.19/5.41  thf('30', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_D_1))),
% 5.19/5.41      inference('sup-', [status(thm)], ['28', '29'])).
% 5.19/5.41  thf('31', plain,
% 5.19/5.41      (((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ (u1_struct_0 @ sk_A))
% 5.19/5.41        | (r2_hidden @ 
% 5.19/5.41           (sk_C @ (u1_struct_0 @ sk_A) @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)) @ 
% 5.19/5.41           (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['25', '30'])).
% 5.19/5.41  thf('32', plain,
% 5.19/5.41      (![X1 : $i, X3 : $i]:
% 5.19/5.41         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_tarski])).
% 5.19/5.41  thf('33', plain,
% 5.19/5.41      ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 5.19/5.41      inference('clc', [status(thm)], ['31', '32'])).
% 5.19/5.41  thf('34', plain,
% 5.19/5.41      (![X13 : $i, X15 : $i]:
% 5.19/5.41         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 5.19/5.41      inference('cnf', [status(esa)], [t3_subset])).
% 5.19/5.41  thf('35', plain,
% 5.19/5.41      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 5.19/5.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['33', '34'])).
% 5.19/5.41  thf('36', plain,
% 5.19/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf(t48_tops_1, axiom,
% 5.19/5.41    (![A:$i]:
% 5.19/5.41     ( ( l1_pre_topc @ A ) =>
% 5.19/5.41       ( ![B:$i]:
% 5.19/5.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.19/5.41           ( ![C:$i]:
% 5.19/5.41             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.19/5.41               ( ( r1_tarski @ B @ C ) =>
% 5.19/5.41                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 5.19/5.41  thf('37', plain,
% 5.19/5.41      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.19/5.41         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 5.19/5.41          | ~ (r1_tarski @ X16 @ X18)
% 5.19/5.41          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ (k1_tops_1 @ X17 @ X18))
% 5.19/5.41          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 5.19/5.41          | ~ (l1_pre_topc @ X17))),
% 5.19/5.41      inference('cnf', [status(esa)], [t48_tops_1])).
% 5.19/5.41  thf('38', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         (~ (l1_pre_topc @ sk_A)
% 5.19/5.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.19/5.41          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 5.19/5.41          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 5.19/5.41      inference('sup-', [status(thm)], ['36', '37'])).
% 5.19/5.41  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('40', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.19/5.41          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 5.19/5.41          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 5.19/5.41      inference('demod', [status(thm)], ['38', '39'])).
% 5.19/5.41  thf('41', plain,
% 5.19/5.41      ((~ (r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1))
% 5.19/5.41        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 5.19/5.41           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1))))),
% 5.19/5.41      inference('sup-', [status(thm)], ['35', '40'])).
% 5.19/5.41  thf('42', plain,
% 5.19/5.41      (![X1 : $i, X3 : $i]:
% 5.19/5.41         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_tarski])).
% 5.19/5.41  thf('43', plain,
% 5.19/5.41      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 5.19/5.41         (~ (r2_hidden @ X4 @ X7)
% 5.19/5.41          | (r2_hidden @ X4 @ X6)
% 5.19/5.41          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.19/5.41  thf('44', plain,
% 5.19/5.41      (![X4 : $i, X5 : $i, X7 : $i]:
% 5.19/5.41         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X7))),
% 5.19/5.41      inference('simplify', [status(thm)], ['43'])).
% 5.19/5.41  thf('45', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         ((r1_tarski @ X0 @ X1)
% 5.19/5.41          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['42', '44'])).
% 5.19/5.41  thf('46', plain,
% 5.19/5.41      (![X1 : $i, X3 : $i]:
% 5.19/5.41         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_tarski])).
% 5.19/5.41  thf('47', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]:
% 5.19/5.41         ((r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 5.19/5.41          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['45', '46'])).
% 5.19/5.41  thf('48', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 5.19/5.41      inference('simplify', [status(thm)], ['47'])).
% 5.19/5.41  thf('49', plain,
% 5.19/5.41      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 5.19/5.41        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 5.19/5.41      inference('demod', [status(thm)], ['41', '48'])).
% 5.19/5.41  thf('50', plain,
% 5.19/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.19/5.41         (~ (r2_hidden @ X0 @ X1)
% 5.19/5.41          | (r2_hidden @ X0 @ X2)
% 5.19/5.41          | ~ (r1_tarski @ X1 @ X2))),
% 5.19/5.41      inference('cnf', [status(esa)], [d3_tarski])).
% 5.19/5.41  thf('51', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((r2_hidden @ X0 @ 
% 5.19/5.41           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 5.19/5.41          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['49', '50'])).
% 5.19/5.41  thf('52', plain,
% 5.19/5.41      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['12', '51'])).
% 5.19/5.41  thf('53', plain,
% 5.19/5.41      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 5.19/5.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['33', '34'])).
% 5.19/5.41  thf('54', plain,
% 5.19/5.41      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.19/5.41         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 5.19/5.41          | ~ (r2_hidden @ X19 @ (k1_tops_1 @ X20 @ X21))
% 5.19/5.41          | (m1_connsp_2 @ X21 @ X20 @ X19)
% 5.19/5.41          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 5.19/5.41          | ~ (l1_pre_topc @ X20)
% 5.19/5.41          | ~ (v2_pre_topc @ X20)
% 5.19/5.41          | (v2_struct_0 @ X20))),
% 5.19/5.41      inference('cnf', [status(esa)], [d1_connsp_2])).
% 5.19/5.41  thf('55', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((v2_struct_0 @ sk_A)
% 5.19/5.41          | ~ (v2_pre_topc @ sk_A)
% 5.19/5.41          | ~ (l1_pre_topc @ sk_A)
% 5.19/5.41          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ X0)
% 5.19/5.41          | ~ (r2_hidden @ X0 @ 
% 5.19/5.41               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 5.19/5.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('sup-', [status(thm)], ['53', '54'])).
% 5.19/5.41  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('58', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         ((v2_struct_0 @ sk_A)
% 5.19/5.41          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ X0)
% 5.19/5.41          | ~ (r2_hidden @ X0 @ 
% 5.19/5.41               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 5.19/5.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('demod', [status(thm)], ['55', '56', '57'])).
% 5.19/5.41  thf('59', plain,
% 5.19/5.41      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.19/5.41        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)
% 5.19/5.41        | (v2_struct_0 @ sk_A))),
% 5.19/5.41      inference('sup-', [status(thm)], ['52', '58'])).
% 5.19/5.41  thf('60', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('61', plain,
% 5.19/5.41      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)
% 5.19/5.41        | (v2_struct_0 @ sk_A))),
% 5.19/5.41      inference('demod', [status(thm)], ['59', '60'])).
% 5.19/5.41  thf('62', plain,
% 5.19/5.41      (~ (m1_connsp_2 @ 
% 5.19/5.41          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('63', plain,
% 5.19/5.41      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf('64', plain,
% 5.19/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.19/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.19/5.41  thf(redefinition_k4_subset_1, axiom,
% 5.19/5.41    (![A:$i,B:$i,C:$i]:
% 5.19/5.41     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.19/5.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.19/5.41       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 5.19/5.41  thf('65', plain,
% 5.19/5.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.19/5.41         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 5.19/5.41          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 5.19/5.41          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 5.19/5.41      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.19/5.41  thf('66', plain,
% 5.19/5.41      (![X0 : $i]:
% 5.19/5.41         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 5.19/5.41            = (k2_xboole_0 @ sk_C_1 @ X0))
% 5.19/5.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.19/5.41      inference('sup-', [status(thm)], ['64', '65'])).
% 5.19/5.41  thf('67', plain,
% 5.19/5.41      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1)
% 5.19/5.41         = (k2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 5.19/5.41      inference('sup-', [status(thm)], ['63', '66'])).
% 5.19/5.41  thf('68', plain,
% 5.19/5.41      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)),
% 5.19/5.41      inference('demod', [status(thm)], ['62', '67'])).
% 5.19/5.41  thf('69', plain, ((v2_struct_0 @ sk_A)),
% 5.19/5.41      inference('clc', [status(thm)], ['61', '68'])).
% 5.19/5.41  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 5.19/5.41  
% 5.19/5.41  % SZS output end Refutation
% 5.19/5.41  
% 5.27/5.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
