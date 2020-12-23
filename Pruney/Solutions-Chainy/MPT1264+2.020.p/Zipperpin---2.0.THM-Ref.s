%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2p90gl5CYz

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:09 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 121 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  674 (1592 expanded)
%              Number of equality atoms :   43 (  77 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t81_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v1_tops_1 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( v3_pre_topc @ C @ A )
                   => ( ( k2_pre_topc @ A @ C )
                      = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) )
                  = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k2_pre_topc @ X21 @ X22 ) ) )
        = ( k2_pre_topc @ X21 @ ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_tops_1 @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','15','18'])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k3_xboole_0 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_hidden @ ( sk_D @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_C )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_C )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('40',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('43',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('47',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','27','28','45','46'])).

thf('48',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('50',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2p90gl5CYz
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:44:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 158 iterations in 0.101s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.56  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.39/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(d3_struct_0, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.56  thf('0', plain,
% 0.39/0.56      (![X16 : $i]:
% 0.39/0.56         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.56  thf(t81_tops_1, conjecture,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56           ( ( v1_tops_1 @ B @ A ) =>
% 0.39/0.56             ( ![C:$i]:
% 0.39/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56                 ( ( v3_pre_topc @ C @ A ) =>
% 0.39/0.56                   ( ( k2_pre_topc @ A @ C ) =
% 0.39/0.56                     ( k2_pre_topc @
% 0.39/0.56                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i]:
% 0.39/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56          ( ![B:$i]:
% 0.39/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56              ( ( v1_tops_1 @ B @ A ) =>
% 0.39/0.56                ( ![C:$i]:
% 0.39/0.56                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56                    ( ( v3_pre_topc @ C @ A ) =>
% 0.39/0.56                      ( ( k2_pre_topc @ A @ C ) =
% 0.39/0.56                        ( k2_pre_topc @
% 0.39/0.56                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t41_tops_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56           ( ![C:$i]:
% 0.39/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56               ( ( v3_pre_topc @ B @ A ) =>
% 0.39/0.56                 ( ( k2_pre_topc @
% 0.39/0.56                     A @ 
% 0.39/0.56                     ( k9_subset_1 @
% 0.39/0.56                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.39/0.56                   ( k2_pre_topc @
% 0.39/0.56                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.39/0.56          | ~ (v3_pre_topc @ X20 @ X21)
% 0.39/0.56          | ((k2_pre_topc @ X21 @ 
% 0.39/0.56              (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 0.39/0.56               (k2_pre_topc @ X21 @ X22)))
% 0.39/0.56              = (k2_pre_topc @ X21 @ 
% 0.39/0.56                 (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X22)))
% 0.39/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.39/0.56          | ~ (l1_pre_topc @ X21)
% 0.39/0.56          | ~ (v2_pre_topc @ X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (v2_pre_topc @ sk_A)
% 0.39/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56          | ((k2_pre_topc @ sk_A @ 
% 0.39/0.56              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.39/0.56               (k2_pre_topc @ sk_A @ X0)))
% 0.39/0.56              = (k2_pre_topc @ sk_A @ 
% 0.39/0.56                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))
% 0.39/0.56          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.56  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('7', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56          | ((k2_pre_topc @ sk_A @ 
% 0.39/0.56              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.39/0.56               (k2_pre_topc @ sk_A @ X0)))
% 0.39/0.56              = (k2_pre_topc @ sk_A @ 
% 0.39/0.56                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 0.39/0.56      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (((k2_pre_topc @ sk_A @ 
% 0.39/0.56         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.39/0.56          (k2_pre_topc @ sk_A @ sk_B)))
% 0.39/0.56         = (k2_pre_topc @ sk_A @ 
% 0.39/0.56            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '8'])).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(d3_tops_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( l1_pre_topc @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56           ( ( v1_tops_1 @ B @ A ) <=>
% 0.39/0.56             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X18 : $i, X19 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.56          | ~ (v1_tops_1 @ X18 @ X19)
% 0.39/0.56          | ((k2_pre_topc @ X19 @ X18) = (k2_struct_0 @ X19))
% 0.39/0.56          | ~ (l1_pre_topc @ X19))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.39/0.56        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.56  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('14', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('15', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k9_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.56         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.39/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.39/0.56           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (((k2_pre_topc @ sk_A @ 
% 0.39/0.56         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.39/0.56         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.39/0.56      inference('demod', [status(thm)], ['9', '15', '18'])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      ((((k2_pre_topc @ sk_A @ 
% 0.39/0.56          (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.39/0.56          = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))
% 0.39/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.56      inference('sup+', [status(thm)], ['0', '19'])).
% 0.39/0.56  thf(dt_k2_subset_1, axiom,
% 0.39/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.39/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.56  thf('22', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.56  thf('23', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.39/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.56         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.39/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.39/0.56  thf('25', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.56  thf(t48_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.56  thf('26', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i]:
% 0.39/0.56         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.39/0.56           = (k3_xboole_0 @ X6 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.56           = (k9_subset_1 @ X0 @ X1 @ X0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['25', '26'])).
% 0.39/0.56  thf('28', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i]:
% 0.39/0.56         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.39/0.56           = (k3_xboole_0 @ X6 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      (![X16 : $i]:
% 0.39/0.56         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.56  thf(d4_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.39/0.56       ( ![D:$i]:
% 0.39/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.39/0.56  thf('30', plain,
% 0.39/0.56      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.39/0.56         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.39/0.56          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.39/0.56          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.39/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.56  thf('31', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.39/0.56          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.39/0.56      inference('eq_fact', [status(thm)], ['30'])).
% 0.39/0.56  thf('32', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(l3_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.56  thf('33', plain,
% 0.39/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X10 @ X11)
% 0.39/0.56          | (r2_hidden @ X10 @ X12)
% 0.39/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.39/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.56  thf('34', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.39/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.56  thf('35', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (((sk_C) = (k3_xboole_0 @ sk_C @ X0))
% 0.39/0.56          | (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['31', '34'])).
% 0.39/0.56  thf('36', plain,
% 0.39/0.56      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.39/0.56         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.39/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.39/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.39/0.56          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.39/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      ((((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.39/0.56        | ~ (r2_hidden @ (sk_D @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_C)
% 0.39/0.56        | ~ (r2_hidden @ (sk_D @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_C)
% 0.39/0.56        | ((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      ((~ (r2_hidden @ (sk_D @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_C)
% 0.39/0.56        | ((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.39/0.56  thf('39', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.39/0.56          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.39/0.56      inference('eq_fact', [status(thm)], ['30'])).
% 0.39/0.56  thf('40', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('clc', [status(thm)], ['38', '39'])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      ((((sk_C) = (k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.39/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.56      inference('sup+', [status(thm)], ['29', '40'])).
% 0.39/0.56  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(dt_l1_pre_topc, axiom,
% 0.39/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.56  thf('43', plain,
% 0.39/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.56  thf('45', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['41', '44'])).
% 0.41/0.56  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.41/0.56  thf('47', plain,
% 0.41/0.56      (((k2_pre_topc @ sk_A @ sk_C)
% 0.41/0.56         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.41/0.56      inference('demod', [status(thm)], ['20', '27', '28', '45', '46'])).
% 0.41/0.56  thf('48', plain,
% 0.41/0.56      (((k2_pre_topc @ sk_A @ sk_C)
% 0.41/0.56         != (k2_pre_topc @ sk_A @ 
% 0.41/0.56             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.41/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.56  thf('49', plain,
% 0.41/0.56      (![X0 : $i]:
% 0.41/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.41/0.56           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.41/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.56  thf('50', plain,
% 0.41/0.56      (((k2_pre_topc @ sk_A @ sk_C)
% 0.41/0.56         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.41/0.56      inference('demod', [status(thm)], ['48', '49'])).
% 0.41/0.56  thf('51', plain, ($false),
% 0.41/0.56      inference('simplify_reflect-', [status(thm)], ['47', '50'])).
% 0.41/0.56  
% 0.41/0.56  % SZS output end Refutation
% 0.41/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
