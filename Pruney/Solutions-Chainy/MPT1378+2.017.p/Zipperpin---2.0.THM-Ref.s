%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLekvxsitl

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:47 EST 2020

% Result     : Theorem 3.64s
% Output     : Refutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 139 expanded)
%              Number of leaves         :   25 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  661 (2111 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    m1_connsp_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) )
      | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) )
      | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ) ),
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

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ X19 @ ( k1_tops_1 @ X20 @ X21 ) )
      | ( m1_connsp_2 @ X21 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['48','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLekvxsitl
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.64/3.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.64/3.88  % Solved by: fo/fo7.sh
% 3.64/3.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.64/3.88  % done 2767 iterations in 3.394s
% 3.64/3.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.64/3.88  % SZS output start Refutation
% 3.64/3.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.64/3.88  thf(sk_D_type, type, sk_D: $i).
% 3.64/3.88  thf(sk_B_type, type, sk_B: $i).
% 3.64/3.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.64/3.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.64/3.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.64/3.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.64/3.88  thf(sk_A_type, type, sk_A: $i).
% 3.64/3.88  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.64/3.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.64/3.88  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.64/3.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.64/3.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.64/3.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.64/3.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.64/3.88  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 3.64/3.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.64/3.88  thf(t3_connsp_2, conjecture,
% 3.64/3.88    (![A:$i]:
% 3.64/3.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.64/3.88       ( ![B:$i]:
% 3.64/3.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.64/3.88           ( ![C:$i]:
% 3.64/3.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.64/3.88               ( ![D:$i]:
% 3.64/3.88                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.64/3.88                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 3.64/3.88                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 3.64/3.88                     ( m1_connsp_2 @
% 3.64/3.88                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 3.64/3.88  thf(zf_stmt_0, negated_conjecture,
% 3.64/3.88    (~( ![A:$i]:
% 3.64/3.88        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.64/3.88            ( l1_pre_topc @ A ) ) =>
% 3.64/3.88          ( ![B:$i]:
% 3.64/3.88            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.64/3.88              ( ![C:$i]:
% 3.64/3.88                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.64/3.88                  ( ![D:$i]:
% 3.64/3.88                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.64/3.88                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 3.64/3.88                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 3.64/3.88                        ( m1_connsp_2 @
% 3.64/3.88                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 3.64/3.88    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 3.64/3.88  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('1', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B)),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('2', plain,
% 3.64/3.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf(d1_connsp_2, axiom,
% 3.64/3.88    (![A:$i]:
% 3.64/3.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.64/3.88       ( ![B:$i]:
% 3.64/3.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.64/3.88           ( ![C:$i]:
% 3.64/3.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.64/3.88               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 3.64/3.88                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.64/3.88  thf('3', plain,
% 3.64/3.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.64/3.88         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.64/3.88          | ~ (m1_connsp_2 @ X21 @ X20 @ X19)
% 3.64/3.88          | (r2_hidden @ X19 @ (k1_tops_1 @ X20 @ X21))
% 3.64/3.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.64/3.88          | ~ (l1_pre_topc @ X20)
% 3.64/3.88          | ~ (v2_pre_topc @ X20)
% 3.64/3.88          | (v2_struct_0 @ X20))),
% 3.64/3.88      inference('cnf', [status(esa)], [d1_connsp_2])).
% 3.64/3.88  thf('4', plain,
% 3.64/3.88      (![X0 : $i]:
% 3.64/3.88         ((v2_struct_0 @ sk_A)
% 3.64/3.88          | ~ (v2_pre_topc @ sk_A)
% 3.64/3.88          | ~ (l1_pre_topc @ sk_A)
% 3.64/3.88          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 3.64/3.88          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 3.64/3.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('sup-', [status(thm)], ['2', '3'])).
% 3.64/3.88  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('7', plain,
% 3.64/3.88      (![X0 : $i]:
% 3.64/3.88         ((v2_struct_0 @ sk_A)
% 3.64/3.88          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 3.64/3.88          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 3.64/3.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('demod', [status(thm)], ['4', '5', '6'])).
% 3.64/3.88  thf('8', plain,
% 3.64/3.88      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.64/3.88        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D))
% 3.64/3.88        | (v2_struct_0 @ sk_A))),
% 3.64/3.88      inference('sup-', [status(thm)], ['1', '7'])).
% 3.64/3.88  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('10', plain,
% 3.64/3.88      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D)) | (v2_struct_0 @ sk_A))),
% 3.64/3.88      inference('demod', [status(thm)], ['8', '9'])).
% 3.64/3.88  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D))),
% 3.64/3.88      inference('clc', [status(thm)], ['10', '11'])).
% 3.64/3.88  thf('13', plain,
% 3.64/3.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf(t3_subset, axiom,
% 3.64/3.88    (![A:$i,B:$i]:
% 3.64/3.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.64/3.88  thf('14', plain,
% 3.64/3.88      (![X13 : $i, X14 : $i]:
% 3.64/3.88         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.64/3.88      inference('cnf', [status(esa)], [t3_subset])).
% 3.64/3.88  thf('15', plain, ((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))),
% 3.64/3.88      inference('sup-', [status(thm)], ['13', '14'])).
% 3.64/3.88  thf('16', plain,
% 3.64/3.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('17', plain,
% 3.64/3.88      (![X13 : $i, X14 : $i]:
% 3.64/3.88         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.64/3.88      inference('cnf', [status(esa)], [t3_subset])).
% 3.64/3.88  thf('18', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 3.64/3.88      inference('sup-', [status(thm)], ['16', '17'])).
% 3.64/3.88  thf(t8_xboole_1, axiom,
% 3.64/3.88    (![A:$i,B:$i,C:$i]:
% 3.64/3.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 3.64/3.88       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.64/3.88  thf('19', plain,
% 3.64/3.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.64/3.88         (~ (r1_tarski @ X7 @ X8)
% 3.64/3.88          | ~ (r1_tarski @ X9 @ X8)
% 3.64/3.88          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 3.64/3.88      inference('cnf', [status(esa)], [t8_xboole_1])).
% 3.64/3.88  thf('20', plain,
% 3.64/3.88      (![X0 : $i]:
% 3.64/3.88         ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A))
% 3.64/3.88          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('sup-', [status(thm)], ['18', '19'])).
% 3.64/3.88  thf('21', plain,
% 3.64/3.88      ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 3.64/3.88      inference('sup-', [status(thm)], ['15', '20'])).
% 3.64/3.88  thf('22', plain,
% 3.64/3.88      (![X13 : $i, X15 : $i]:
% 3.64/3.88         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 3.64/3.88      inference('cnf', [status(esa)], [t3_subset])).
% 3.64/3.88  thf('23', plain,
% 3.64/3.88      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 3.64/3.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('sup-', [status(thm)], ['21', '22'])).
% 3.64/3.88  thf('24', plain,
% 3.64/3.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf(t48_tops_1, axiom,
% 3.64/3.88    (![A:$i]:
% 3.64/3.88     ( ( l1_pre_topc @ A ) =>
% 3.64/3.88       ( ![B:$i]:
% 3.64/3.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.64/3.88           ( ![C:$i]:
% 3.64/3.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.64/3.88               ( ( r1_tarski @ B @ C ) =>
% 3.64/3.88                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.64/3.88  thf('25', plain,
% 3.64/3.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.64/3.88         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.64/3.88          | ~ (r1_tarski @ X16 @ X18)
% 3.64/3.88          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ (k1_tops_1 @ X17 @ X18))
% 3.64/3.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.64/3.88          | ~ (l1_pre_topc @ X17))),
% 3.64/3.88      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.64/3.88  thf('26', plain,
% 3.64/3.88      (![X0 : $i]:
% 3.64/3.88         (~ (l1_pre_topc @ sk_A)
% 3.64/3.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.64/3.88          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 3.64/3.88          | ~ (r1_tarski @ sk_D @ X0))),
% 3.64/3.88      inference('sup-', [status(thm)], ['24', '25'])).
% 3.64/3.88  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('28', plain,
% 3.64/3.88      (![X0 : $i]:
% 3.64/3.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.64/3.88          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 3.64/3.88          | ~ (r1_tarski @ sk_D @ X0))),
% 3.64/3.88      inference('demod', [status(thm)], ['26', '27'])).
% 3.64/3.88  thf('29', plain,
% 3.64/3.88      ((~ (r1_tarski @ sk_D @ (k2_xboole_0 @ sk_C_1 @ sk_D))
% 3.64/3.88        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 3.64/3.88           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D))))),
% 3.64/3.88      inference('sup-', [status(thm)], ['23', '28'])).
% 3.64/3.88  thf(d3_tarski, axiom,
% 3.64/3.88    (![A:$i,B:$i]:
% 3.64/3.88     ( ( r1_tarski @ A @ B ) <=>
% 3.64/3.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.64/3.88  thf('30', plain,
% 3.64/3.88      (![X1 : $i, X3 : $i]:
% 3.64/3.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.64/3.88      inference('cnf', [status(esa)], [d3_tarski])).
% 3.64/3.88  thf('31', plain,
% 3.64/3.88      (![X1 : $i, X3 : $i]:
% 3.64/3.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.64/3.88      inference('cnf', [status(esa)], [d3_tarski])).
% 3.64/3.88  thf('32', plain,
% 3.64/3.88      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 3.64/3.88      inference('sup-', [status(thm)], ['30', '31'])).
% 3.64/3.88  thf('33', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.64/3.88      inference('simplify', [status(thm)], ['32'])).
% 3.64/3.88  thf(t10_xboole_1, axiom,
% 3.64/3.88    (![A:$i,B:$i,C:$i]:
% 3.64/3.88     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 3.64/3.88  thf('34', plain,
% 3.64/3.88      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.64/3.88         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 3.64/3.88      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.64/3.88  thf('35', plain,
% 3.64/3.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.64/3.88      inference('sup-', [status(thm)], ['33', '34'])).
% 3.64/3.88  thf('36', plain,
% 3.64/3.88      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 3.64/3.88        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 3.64/3.88      inference('demod', [status(thm)], ['29', '35'])).
% 3.64/3.88  thf('37', plain,
% 3.64/3.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.64/3.88         (~ (r2_hidden @ X0 @ X1)
% 3.64/3.88          | (r2_hidden @ X0 @ X2)
% 3.64/3.88          | ~ (r1_tarski @ X1 @ X2))),
% 3.64/3.88      inference('cnf', [status(esa)], [d3_tarski])).
% 3.64/3.88  thf('38', plain,
% 3.64/3.88      (![X0 : $i]:
% 3.64/3.88         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 3.64/3.88          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D)))),
% 3.64/3.88      inference('sup-', [status(thm)], ['36', '37'])).
% 3.64/3.88  thf('39', plain,
% 3.64/3.88      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 3.64/3.88      inference('sup-', [status(thm)], ['12', '38'])).
% 3.64/3.88  thf('40', plain,
% 3.64/3.88      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 3.64/3.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('sup-', [status(thm)], ['21', '22'])).
% 3.64/3.88  thf('41', plain,
% 3.64/3.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.64/3.88         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.64/3.88          | ~ (r2_hidden @ X19 @ (k1_tops_1 @ X20 @ X21))
% 3.64/3.88          | (m1_connsp_2 @ X21 @ X20 @ X19)
% 3.64/3.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.64/3.88          | ~ (l1_pre_topc @ X20)
% 3.64/3.88          | ~ (v2_pre_topc @ X20)
% 3.64/3.88          | (v2_struct_0 @ X20))),
% 3.64/3.88      inference('cnf', [status(esa)], [d1_connsp_2])).
% 3.64/3.88  thf('42', plain,
% 3.64/3.88      (![X0 : $i]:
% 3.64/3.88         ((v2_struct_0 @ sk_A)
% 3.64/3.88          | ~ (v2_pre_topc @ sk_A)
% 3.64/3.88          | ~ (l1_pre_topc @ sk_A)
% 3.64/3.88          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 3.64/3.88          | ~ (r2_hidden @ X0 @ 
% 3.64/3.88               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 3.64/3.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('sup-', [status(thm)], ['40', '41'])).
% 3.64/3.88  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('45', plain,
% 3.64/3.88      (![X0 : $i]:
% 3.64/3.88         ((v2_struct_0 @ sk_A)
% 3.64/3.88          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 3.64/3.88          | ~ (r2_hidden @ X0 @ 
% 3.64/3.88               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 3.64/3.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('demod', [status(thm)], ['42', '43', '44'])).
% 3.64/3.88  thf('46', plain,
% 3.64/3.88      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.64/3.88        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 3.64/3.88        | (v2_struct_0 @ sk_A))),
% 3.64/3.88      inference('sup-', [status(thm)], ['39', '45'])).
% 3.64/3.88  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('48', plain,
% 3.64/3.88      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 3.64/3.88        | (v2_struct_0 @ sk_A))),
% 3.64/3.88      inference('demod', [status(thm)], ['46', '47'])).
% 3.64/3.88  thf('49', plain,
% 3.64/3.88      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D) @ 
% 3.64/3.88          sk_A @ sk_B)),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('50', plain,
% 3.64/3.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf('51', plain,
% 3.64/3.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.64/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.64/3.88  thf(redefinition_k4_subset_1, axiom,
% 3.64/3.88    (![A:$i,B:$i,C:$i]:
% 3.64/3.88     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.64/3.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.64/3.88       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.64/3.88  thf('52', plain,
% 3.64/3.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.64/3.88         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 3.64/3.88          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 3.64/3.88          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 3.64/3.88      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.64/3.88  thf('53', plain,
% 3.64/3.88      (![X0 : $i]:
% 3.64/3.88         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 3.64/3.88            = (k2_xboole_0 @ sk_C_1 @ X0))
% 3.64/3.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.64/3.88      inference('sup-', [status(thm)], ['51', '52'])).
% 3.64/3.88  thf('54', plain,
% 3.64/3.88      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D)
% 3.64/3.88         = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 3.64/3.88      inference('sup-', [status(thm)], ['50', '53'])).
% 3.64/3.88  thf('55', plain,
% 3.64/3.88      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)),
% 3.64/3.88      inference('demod', [status(thm)], ['49', '54'])).
% 3.64/3.88  thf('56', plain, ((v2_struct_0 @ sk_A)),
% 3.64/3.88      inference('clc', [status(thm)], ['48', '55'])).
% 3.64/3.88  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 3.64/3.88  
% 3.64/3.88  % SZS output end Refutation
% 3.64/3.88  
% 3.64/3.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
