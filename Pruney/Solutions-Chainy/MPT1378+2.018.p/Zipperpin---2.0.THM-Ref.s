%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.18r8qSvI5c

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:47 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 131 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  625 (2057 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ( r2_hidden @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X8 @ X7 )
      | ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
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
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['43','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.18r8qSvI5c
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:29:56 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.51/1.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.51/1.72  % Solved by: fo/fo7.sh
% 1.51/1.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.72  % done 1950 iterations in 1.261s
% 1.51/1.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.51/1.72  % SZS output start Refutation
% 1.51/1.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.51/1.72  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.51/1.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.51/1.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.72  thf(sk_D_type, type, sk_D: $i).
% 1.51/1.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.51/1.72  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.72  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.51/1.72  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.51/1.72  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 1.51/1.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.51/1.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.51/1.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.72  thf(t3_connsp_2, conjecture,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.51/1.72       ( ![B:$i]:
% 1.51/1.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.51/1.72           ( ![C:$i]:
% 1.51/1.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.72               ( ![D:$i]:
% 1.51/1.72                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.72                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 1.51/1.72                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 1.51/1.72                     ( m1_connsp_2 @
% 1.51/1.72                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 1.51/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.72    (~( ![A:$i]:
% 1.51/1.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.51/1.72            ( l1_pre_topc @ A ) ) =>
% 1.51/1.72          ( ![B:$i]:
% 1.51/1.72            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.51/1.72              ( ![C:$i]:
% 1.51/1.72                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.72                  ( ![D:$i]:
% 1.51/1.72                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.72                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 1.51/1.72                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 1.51/1.72                        ( m1_connsp_2 @
% 1.51/1.72                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 1.51/1.72    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 1.51/1.72  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('1', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('2', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(d1_connsp_2, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.51/1.72       ( ![B:$i]:
% 1.51/1.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.51/1.72           ( ![C:$i]:
% 1.51/1.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.72               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 1.51/1.72                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.51/1.72  thf('3', plain,
% 1.51/1.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 1.51/1.72          | ~ (m1_connsp_2 @ X20 @ X19 @ X18)
% 1.51/1.72          | (r2_hidden @ X18 @ (k1_tops_1 @ X19 @ X20))
% 1.51/1.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.51/1.72          | ~ (l1_pre_topc @ X19)
% 1.51/1.72          | ~ (v2_pre_topc @ X19)
% 1.51/1.72          | (v2_struct_0 @ X19))),
% 1.51/1.72      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.51/1.72  thf('4', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         ((v2_struct_0 @ sk_A)
% 1.51/1.72          | ~ (v2_pre_topc @ sk_A)
% 1.51/1.72          | ~ (l1_pre_topc @ sk_A)
% 1.51/1.72          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.51/1.72          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.72  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('7', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         ((v2_struct_0 @ sk_A)
% 1.51/1.72          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.51/1.72          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('demod', [status(thm)], ['4', '5', '6'])).
% 1.51/1.72  thf('8', plain,
% 1.51/1.72      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.51/1.72        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.51/1.72        | (v2_struct_0 @ sk_A))),
% 1.51/1.72      inference('sup-', [status(thm)], ['1', '7'])).
% 1.51/1.72  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('10', plain,
% 1.51/1.72      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 1.51/1.72      inference('demod', [status(thm)], ['8', '9'])).
% 1.51/1.72  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.51/1.72      inference('clc', [status(thm)], ['10', '11'])).
% 1.51/1.72  thf('13', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(t3_subset, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.51/1.72  thf('14', plain,
% 1.51/1.72      (![X12 : $i, X13 : $i]:
% 1.51/1.72         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.51/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.72  thf('15', plain, ((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))),
% 1.51/1.72      inference('sup-', [status(thm)], ['13', '14'])).
% 1.51/1.72  thf('16', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('17', plain,
% 1.51/1.72      (![X12 : $i, X13 : $i]:
% 1.51/1.72         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.51/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.72  thf('18', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.51/1.72      inference('sup-', [status(thm)], ['16', '17'])).
% 1.51/1.72  thf(t8_xboole_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.51/1.72       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.51/1.72  thf('19', plain,
% 1.51/1.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.51/1.72         (~ (r1_tarski @ X6 @ X7)
% 1.51/1.72          | ~ (r1_tarski @ X8 @ X7)
% 1.51/1.72          | (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 1.51/1.72      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.51/1.72  thf('20', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A))
% 1.51/1.72          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['18', '19'])).
% 1.51/1.72  thf('21', plain,
% 1.51/1.72      ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 1.51/1.72      inference('sup-', [status(thm)], ['15', '20'])).
% 1.51/1.72  thf('22', plain,
% 1.51/1.72      (![X12 : $i, X14 : $i]:
% 1.51/1.72         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 1.51/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.72  thf('23', plain,
% 1.51/1.72      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 1.51/1.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['21', '22'])).
% 1.51/1.72  thf('24', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(t48_tops_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( l1_pre_topc @ A ) =>
% 1.51/1.72       ( ![B:$i]:
% 1.51/1.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.72           ( ![C:$i]:
% 1.51/1.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.72               ( ( r1_tarski @ B @ C ) =>
% 1.51/1.72                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.51/1.72  thf('25', plain,
% 1.51/1.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.51/1.72          | ~ (r1_tarski @ X15 @ X17)
% 1.51/1.72          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ (k1_tops_1 @ X16 @ X17))
% 1.51/1.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.51/1.72          | ~ (l1_pre_topc @ X16))),
% 1.51/1.72      inference('cnf', [status(esa)], [t48_tops_1])).
% 1.51/1.72  thf('26', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (~ (l1_pre_topc @ sk_A)
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.51/1.72          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 1.51/1.72          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 1.51/1.72      inference('sup-', [status(thm)], ['24', '25'])).
% 1.51/1.72  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('28', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.51/1.72          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 1.51/1.72          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 1.51/1.72      inference('demod', [status(thm)], ['26', '27'])).
% 1.51/1.72  thf('29', plain,
% 1.51/1.72      ((~ (r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D))
% 1.51/1.72        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.51/1.72           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D))))),
% 1.51/1.72      inference('sup-', [status(thm)], ['23', '28'])).
% 1.51/1.72  thf(t7_xboole_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.51/1.72  thf('30', plain,
% 1.51/1.72      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 1.51/1.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.51/1.72  thf('31', plain,
% 1.51/1.72      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.51/1.72        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 1.51/1.72      inference('demod', [status(thm)], ['29', '30'])).
% 1.51/1.72  thf(d3_tarski, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( r1_tarski @ A @ B ) <=>
% 1.51/1.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.51/1.72  thf('32', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         (~ (r2_hidden @ X0 @ X1)
% 1.51/1.72          | (r2_hidden @ X0 @ X2)
% 1.51/1.72          | ~ (r1_tarski @ X1 @ X2))),
% 1.51/1.72      inference('cnf', [status(esa)], [d3_tarski])).
% 1.51/1.72  thf('33', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 1.51/1.72          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['31', '32'])).
% 1.51/1.72  thf('34', plain,
% 1.51/1.72      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['12', '33'])).
% 1.51/1.72  thf('35', plain,
% 1.51/1.72      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 1.51/1.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['21', '22'])).
% 1.51/1.72  thf('36', plain,
% 1.51/1.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 1.51/1.72          | ~ (r2_hidden @ X18 @ (k1_tops_1 @ X19 @ X20))
% 1.51/1.72          | (m1_connsp_2 @ X20 @ X19 @ X18)
% 1.51/1.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.51/1.72          | ~ (l1_pre_topc @ X19)
% 1.51/1.72          | ~ (v2_pre_topc @ X19)
% 1.51/1.72          | (v2_struct_0 @ X19))),
% 1.51/1.72      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.51/1.72  thf('37', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         ((v2_struct_0 @ sk_A)
% 1.51/1.72          | ~ (v2_pre_topc @ sk_A)
% 1.51/1.72          | ~ (l1_pre_topc @ sk_A)
% 1.51/1.72          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 1.51/1.72          | ~ (r2_hidden @ X0 @ 
% 1.51/1.72               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['35', '36'])).
% 1.51/1.72  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('40', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         ((v2_struct_0 @ sk_A)
% 1.51/1.72          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 1.51/1.72          | ~ (r2_hidden @ X0 @ 
% 1.51/1.72               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.51/1.72  thf('41', plain,
% 1.51/1.72      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.51/1.72        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 1.51/1.72        | (v2_struct_0 @ sk_A))),
% 1.51/1.72      inference('sup-', [status(thm)], ['34', '40'])).
% 1.51/1.72  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('43', plain,
% 1.51/1.72      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 1.51/1.72        | (v2_struct_0 @ sk_A))),
% 1.51/1.72      inference('demod', [status(thm)], ['41', '42'])).
% 1.51/1.72  thf('44', plain,
% 1.51/1.72      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D) @ 
% 1.51/1.72          sk_A @ sk_B)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('45', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('46', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(redefinition_k4_subset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.51/1.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.51/1.72       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.51/1.72  thf('47', plain,
% 1.51/1.72      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 1.51/1.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 1.51/1.72          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.51/1.72  thf('48', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 1.51/1.72            = (k2_xboole_0 @ sk_C_1 @ X0))
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.51/1.72      inference('sup-', [status(thm)], ['46', '47'])).
% 1.51/1.72  thf('49', plain,
% 1.51/1.72      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D)
% 1.51/1.72         = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 1.51/1.72      inference('sup-', [status(thm)], ['45', '48'])).
% 1.51/1.72  thf('50', plain,
% 1.51/1.72      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)),
% 1.51/1.72      inference('demod', [status(thm)], ['44', '49'])).
% 1.51/1.72  thf('51', plain, ((v2_struct_0 @ sk_A)),
% 1.51/1.72      inference('clc', [status(thm)], ['43', '50'])).
% 1.51/1.72  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 1.51/1.72  
% 1.51/1.72  % SZS output end Refutation
% 1.51/1.72  
% 1.51/1.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
