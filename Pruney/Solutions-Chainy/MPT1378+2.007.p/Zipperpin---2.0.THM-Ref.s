%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ASwLMtws7s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:46 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 135 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  654 (2086 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ( r2_hidden @ X22 @ ( k1_tops_1 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
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
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( r1_tarski @ ( k1_tops_1 @ X20 @ X19 ) @ ( k1_tops_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_hidden @ X22 @ ( k1_tops_1 @ X23 @ X24 ) )
      | ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
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
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['46','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ASwLMtws7s
% 0.17/0.37  % Computer   : n005.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 12:40:33 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.77/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.95  % Solved by: fo/fo7.sh
% 0.77/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.95  % done 1166 iterations in 0.468s
% 0.77/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.95  % SZS output start Refutation
% 0.77/0.95  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.77/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.95  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.77/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.95  thf(sk_D_type, type, sk_D: $i).
% 0.77/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.77/0.95  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.77/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.95  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.77/0.95  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.77/0.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.95  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.77/0.95  thf(t3_connsp_2, conjecture,
% 0.77/0.95    (![A:$i]:
% 0.77/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.95       ( ![B:$i]:
% 0.77/0.95         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.77/0.95           ( ![C:$i]:
% 0.77/0.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.95               ( ![D:$i]:
% 0.77/0.95                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.95                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.77/0.95                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.77/0.95                     ( m1_connsp_2 @
% 0.77/0.95                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.77/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.95    (~( ![A:$i]:
% 0.77/0.95        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.77/0.95            ( l1_pre_topc @ A ) ) =>
% 0.77/0.95          ( ![B:$i]:
% 0.77/0.95            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.77/0.95              ( ![C:$i]:
% 0.77/0.95                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.95                  ( ![D:$i]:
% 0.77/0.95                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.95                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.77/0.95                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.77/0.95                        ( m1_connsp_2 @
% 0.77/0.95                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.77/0.95    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 0.77/0.95  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('1', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('2', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(d1_connsp_2, axiom,
% 0.77/0.95    (![A:$i]:
% 0.77/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.95       ( ![B:$i]:
% 0.77/0.95         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.77/0.95           ( ![C:$i]:
% 0.77/0.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.95               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.77/0.95                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.77/0.95  thf('3', plain,
% 0.77/0.95      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.77/0.95          | ~ (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.77/0.95          | (r2_hidden @ X22 @ (k1_tops_1 @ X23 @ X24))
% 0.77/0.95          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.77/0.95          | ~ (l1_pre_topc @ X23)
% 0.77/0.95          | ~ (v2_pre_topc @ X23)
% 0.77/0.95          | (v2_struct_0 @ X23))),
% 0.77/0.95      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.77/0.95  thf('4', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v2_struct_0 @ sk_A)
% 0.77/0.95          | ~ (v2_pre_topc @ sk_A)
% 0.77/0.95          | ~ (l1_pre_topc @ sk_A)
% 0.77/0.95          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.77/0.95          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.95  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('7', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v2_struct_0 @ sk_A)
% 0.77/0.95          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.77/0.95          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.77/0.95  thf('8', plain,
% 0.77/0.95      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.77/0.95        | (v2_struct_0 @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['1', '7'])).
% 0.77/0.95  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('10', plain,
% 0.77/0.95      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.77/0.95      inference('demod', [status(thm)], ['8', '9'])).
% 0.77/0.95  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.77/0.95      inference('clc', [status(thm)], ['10', '11'])).
% 0.77/0.95  thf('13', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(t3_subset, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/0.95  thf('14', plain,
% 0.77/0.95      (![X16 : $i, X17 : $i]:
% 0.77/0.95         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.95  thf('15', plain, ((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('16', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('17', plain,
% 0.77/0.95      (![X16 : $i, X17 : $i]:
% 0.77/0.95         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.95  thf('18', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['16', '17'])).
% 0.77/0.95  thf(t8_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.77/0.95       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.77/0.95  thf('19', plain,
% 0.77/0.95      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/0.95         (~ (r1_tarski @ X10 @ X11)
% 0.77/0.95          | ~ (r1_tarski @ X12 @ X11)
% 0.77/0.95          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.77/0.95      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.77/0.95  thf('20', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['18', '19'])).
% 0.77/0.95  thf('21', plain,
% 0.77/0.95      ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['15', '20'])).
% 0.77/0.95  thf('22', plain,
% 0.77/0.95      (![X16 : $i, X18 : $i]:
% 0.77/0.95         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.77/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.95  thf('23', plain,
% 0.77/0.95      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 0.77/0.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.77/0.95  thf('24', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(t48_tops_1, axiom,
% 0.77/0.95    (![A:$i]:
% 0.77/0.95     ( ( l1_pre_topc @ A ) =>
% 0.77/0.95       ( ![B:$i]:
% 0.77/0.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.95           ( ![C:$i]:
% 0.77/0.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.95               ( ( r1_tarski @ B @ C ) =>
% 0.77/0.95                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.77/0.95  thf('25', plain,
% 0.77/0.95      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.77/0.95          | ~ (r1_tarski @ X19 @ X21)
% 0.77/0.95          | (r1_tarski @ (k1_tops_1 @ X20 @ X19) @ (k1_tops_1 @ X20 @ X21))
% 0.77/0.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.77/0.95          | ~ (l1_pre_topc @ X20))),
% 0.77/0.95      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.77/0.95  thf('26', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         (~ (l1_pre_topc @ sk_A)
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.95          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.77/0.95          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.77/0.95      inference('sup-', [status(thm)], ['24', '25'])).
% 0.77/0.95  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('28', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.95          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.77/0.95          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.77/0.95      inference('demod', [status(thm)], ['26', '27'])).
% 0.77/0.95  thf('29', plain,
% 0.77/0.95      ((~ (r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D))
% 0.77/0.95        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.95           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['23', '28'])).
% 0.77/0.95  thf(d10_xboole_0, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.95  thf('30', plain,
% 0.77/0.95      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.77/0.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.95  thf('31', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.77/0.95      inference('simplify', [status(thm)], ['30'])).
% 0.77/0.95  thf(t11_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.77/0.95  thf('32', plain,
% 0.77/0.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.77/0.95         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.77/0.95      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.77/0.95  thf('33', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/0.95      inference('sup-', [status(thm)], ['31', '32'])).
% 0.77/0.95  thf('34', plain,
% 0.77/0.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.95        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.77/0.95      inference('demod', [status(thm)], ['29', '33'])).
% 0.77/0.95  thf(d3_tarski, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( r1_tarski @ A @ B ) <=>
% 0.77/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.77/0.95  thf('35', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X0 @ X1)
% 0.77/0.95          | (r2_hidden @ X0 @ X2)
% 0.77/0.95          | ~ (r1_tarski @ X1 @ X2))),
% 0.77/0.95      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.95  thf('36', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 0.77/0.95          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/0.95  thf('37', plain,
% 0.77/0.95      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['12', '36'])).
% 0.77/0.95  thf('38', plain,
% 0.77/0.95      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 0.77/0.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.77/0.95  thf('39', plain,
% 0.77/0.95      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.77/0.95          | ~ (r2_hidden @ X22 @ (k1_tops_1 @ X23 @ X24))
% 0.77/0.95          | (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.77/0.95          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.77/0.95          | ~ (l1_pre_topc @ X23)
% 0.77/0.95          | ~ (v2_pre_topc @ X23)
% 0.77/0.95          | (v2_struct_0 @ X23))),
% 0.77/0.95      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.77/0.95  thf('40', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v2_struct_0 @ sk_A)
% 0.77/0.95          | ~ (v2_pre_topc @ sk_A)
% 0.77/0.95          | ~ (l1_pre_topc @ sk_A)
% 0.77/0.95          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 0.77/0.95          | ~ (r2_hidden @ X0 @ 
% 0.77/0.95               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/0.95  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('43', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v2_struct_0 @ sk_A)
% 0.77/0.95          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 0.77/0.95          | ~ (r2_hidden @ X0 @ 
% 0.77/0.95               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.77/0.95  thf('44', plain,
% 0.77/0.95      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 0.77/0.95        | (v2_struct_0 @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['37', '43'])).
% 0.77/0.95  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('46', plain,
% 0.77/0.95      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 0.77/0.95        | (v2_struct_0 @ sk_A))),
% 0.77/0.95      inference('demod', [status(thm)], ['44', '45'])).
% 0.77/0.95  thf('47', plain,
% 0.77/0.95      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D) @ 
% 0.77/0.95          sk_A @ sk_B)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('48', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('49', plain,
% 0.77/0.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(redefinition_k4_subset_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.77/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.77/0.95       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.77/0.95  thf('50', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.77/0.95          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.77/0.95          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.77/0.95      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.77/0.95  thf('51', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 0.77/0.95            = (k2_xboole_0 @ sk_C_1 @ X0))
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['49', '50'])).
% 0.77/0.95  thf('52', plain,
% 0.77/0.95      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D)
% 0.77/0.95         = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.77/0.95      inference('sup-', [status(thm)], ['48', '51'])).
% 0.77/0.95  thf('53', plain,
% 0.77/0.95      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)),
% 0.77/0.95      inference('demod', [status(thm)], ['47', '52'])).
% 0.77/0.95  thf('54', plain, ((v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('clc', [status(thm)], ['46', '53'])).
% 0.77/0.95  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 0.77/0.95  
% 0.77/0.95  % SZS output end Refutation
% 0.77/0.95  
% 0.77/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
