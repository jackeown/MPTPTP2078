%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BiGadw8Rcp

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:47 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 139 expanded)
%              Number of leaves         :   25 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  638 (2430 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X12 @ X11 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k4_subset_1 @ X15 @ X14 @ X16 )
        = ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('48',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['45','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BiGadw8Rcp
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.54/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.77  % Solved by: fo/fo7.sh
% 0.54/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.77  % done 323 iterations in 0.322s
% 0.54/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.77  % SZS output start Refutation
% 0.54/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.54/0.77  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.54/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.54/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.77  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.54/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.54/0.77  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.54/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.77  thf(t3_connsp_2, conjecture,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77               ( ![D:$i]:
% 0.54/0.77                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.54/0.77                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.54/0.77                     ( m1_connsp_2 @
% 0.54/0.77                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.77    (~( ![A:$i]:
% 0.54/0.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.54/0.77            ( l1_pre_topc @ A ) ) =>
% 0.54/0.77          ( ![B:$i]:
% 0.54/0.77            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77              ( ![C:$i]:
% 0.54/0.77                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77                  ( ![D:$i]:
% 0.54/0.77                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.54/0.77                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.54/0.77                        ( m1_connsp_2 @
% 0.54/0.77                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.54/0.77    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 0.54/0.77  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('1', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('2', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(d1_connsp_2, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.54/0.77                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf('3', plain,
% 0.54/0.77      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.54/0.77          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.54/0.77          | (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 0.54/0.77          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.54/0.77          | ~ (l1_pre_topc @ X21)
% 0.54/0.77          | ~ (v2_pre_topc @ X21)
% 0.54/0.77          | (v2_struct_0 @ X21))),
% 0.54/0.77      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.54/0.77  thf('4', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.54/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.54/0.77          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 0.54/0.77          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.77  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('7', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 0.54/0.77          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.54/0.77  thf('8', plain,
% 0.54/0.77      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.54/0.77        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D))
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['1', '7'])).
% 0.54/0.77  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('10', plain,
% 0.54/0.77      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D)) | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.77  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D))),
% 0.54/0.77      inference('clc', [status(thm)], ['10', '11'])).
% 0.54/0.77  thf('13', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('14', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(dt_k4_subset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.54/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.77       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.54/0.77  thf('15', plain,
% 0.54/0.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.54/0.77          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 0.54/0.77          | (m1_subset_1 @ (k4_subset_1 @ X12 @ X11 @ X13) @ 
% 0.54/0.77             (k1_zfmisc_1 @ X12)))),
% 0.54/0.77      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.54/0.77  thf('16', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0) @ 
% 0.54/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.77  thf('17', plain,
% 0.54/0.77      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D) @ 
% 0.54/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['13', '16'])).
% 0.54/0.77  thf('18', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('19', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(redefinition_k4_subset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.54/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.77       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.54/0.77  thf('20', plain,
% 0.54/0.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.54/0.77          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 0.54/0.77          | ((k4_subset_1 @ X15 @ X14 @ X16) = (k2_xboole_0 @ X14 @ X16)))),
% 0.54/0.77      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.54/0.77  thf('21', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 0.54/0.77            = (k2_xboole_0 @ sk_C_1 @ X0))
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.77  thf('22', plain,
% 0.54/0.77      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D)
% 0.54/0.77         = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.54/0.77      inference('sup-', [status(thm)], ['18', '21'])).
% 0.54/0.77  thf('23', plain,
% 0.54/0.77      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 0.54/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('demod', [status(thm)], ['17', '22'])).
% 0.54/0.77  thf('24', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(t48_tops_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( l1_pre_topc @ A ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77               ( ( r1_tarski @ B @ C ) =>
% 0.54/0.77                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf('25', plain,
% 0.54/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.54/0.77          | ~ (r1_tarski @ X17 @ X19)
% 0.54/0.77          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ (k1_tops_1 @ X18 @ X19))
% 0.54/0.77          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.54/0.77          | ~ (l1_pre_topc @ X18))),
% 0.54/0.77      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.54/0.77  thf('26', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (l1_pre_topc @ sk_A)
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.77          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.54/0.77          | ~ (r1_tarski @ sk_D @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.77  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('28', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.77          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.54/0.77          | ~ (r1_tarski @ sk_D @ X0))),
% 0.54/0.77      inference('demod', [status(thm)], ['26', '27'])).
% 0.54/0.77  thf('29', plain,
% 0.54/0.77      ((~ (r1_tarski @ sk_D @ (k2_xboole_0 @ sk_C_1 @ sk_D))
% 0.54/0.77        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 0.54/0.77           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['23', '28'])).
% 0.54/0.77  thf(t36_xboole_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.77  thf('30', plain,
% 0.54/0.77      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.54/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.54/0.77  thf(t44_xboole_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.54/0.77       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.54/0.77  thf('31', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.54/0.77         ((r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 0.54/0.77          | ~ (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X8))),
% 0.54/0.77      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.54/0.77  thf('32', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.77  thf('33', plain,
% 0.54/0.77      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 0.54/0.77        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.54/0.77      inference('demod', [status(thm)], ['29', '32'])).
% 0.54/0.77  thf(d3_tarski, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.77  thf('34', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X0 @ X1)
% 0.54/0.77          | (r2_hidden @ X0 @ X2)
% 0.54/0.77          | ~ (r1_tarski @ X1 @ X2))),
% 0.54/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.77  thf('35', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 0.54/0.77          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.77  thf('36', plain,
% 0.54/0.77      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['12', '35'])).
% 0.54/0.77  thf('37', plain,
% 0.54/0.77      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 0.54/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('demod', [status(thm)], ['17', '22'])).
% 0.54/0.77  thf('38', plain,
% 0.54/0.77      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.54/0.77          | ~ (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 0.54/0.77          | (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.54/0.77          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.54/0.77          | ~ (l1_pre_topc @ X21)
% 0.54/0.77          | ~ (v2_pre_topc @ X21)
% 0.54/0.77          | (v2_struct_0 @ X21))),
% 0.54/0.77      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.54/0.77  thf('39', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.54/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.54/0.77          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 0.54/0.77          | ~ (r2_hidden @ X0 @ 
% 0.54/0.77               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.77  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('42', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 0.54/0.77          | ~ (r2_hidden @ X0 @ 
% 0.54/0.77               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.54/0.77  thf('43', plain,
% 0.54/0.77      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.54/0.77        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['36', '42'])).
% 0.54/0.77  thf('44', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('45', plain,
% 0.54/0.77      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['43', '44'])).
% 0.54/0.77  thf('46', plain,
% 0.54/0.77      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D) @ 
% 0.54/0.77          sk_A @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('47', plain,
% 0.54/0.77      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D)
% 0.54/0.77         = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.54/0.77      inference('sup-', [status(thm)], ['18', '21'])).
% 0.54/0.77  thf('48', plain,
% 0.54/0.77      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)),
% 0.54/0.77      inference('demod', [status(thm)], ['46', '47'])).
% 0.54/0.77  thf('49', plain, ((v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('clc', [status(thm)], ['45', '48'])).
% 0.54/0.77  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.54/0.77  
% 0.54/0.77  % SZS output end Refutation
% 0.54/0.77  
% 0.64/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
