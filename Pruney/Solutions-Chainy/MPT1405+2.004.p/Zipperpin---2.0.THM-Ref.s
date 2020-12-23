%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wtnvXyxX9I

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:14 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 128 expanded)
%              Number of leaves         :   32 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  576 (1252 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( ( k1_tops_1 @ X19 @ ( k2_struct_0 @ X19 ) )
        = ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ( m2_connsp_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('18',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['18','19'])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( r1_tarski @ ( k2_struct_0 @ X8 ) @ ( k2_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X2
       != ( k1_pre_topc @ X1 @ X0 ) )
      | ( ( k2_struct_0 @ X2 )
        = X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) @ X1 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X1 @ X0 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('33',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['18','19'])).

thf('38',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['18','19'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','38','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['15','44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wtnvXyxX9I
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 210 iterations in 0.164s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.43/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.43/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.62  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.43/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.43/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.43/0.62  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.43/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.43/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.43/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.62  thf(t43_tops_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (![X19 : $i]:
% 0.43/0.62         (((k1_tops_1 @ X19 @ (k2_struct_0 @ X19)) = (k2_struct_0 @ X19))
% 0.43/0.62          | ~ (l1_pre_topc @ X19)
% 0.43/0.62          | ~ (v2_pre_topc @ X19))),
% 0.43/0.62      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.43/0.62  thf(dt_k2_struct_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_struct_0 @ A ) =>
% 0.43/0.62       ( m1_subset_1 @
% 0.43/0.62         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X15 : $i]:
% 0.43/0.62         ((m1_subset_1 @ (k2_struct_0 @ X15) @ 
% 0.43/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.43/0.62          | ~ (l1_struct_0 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.43/0.62  thf(t35_connsp_2, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.43/0.62            ( l1_pre_topc @ A ) ) =>
% 0.43/0.62          ( ![B:$i]:
% 0.43/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d2_connsp_2, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.43/0.62                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.62          | ~ (r1_tarski @ X20 @ (k1_tops_1 @ X21 @ X22))
% 0.43/0.62          | (m2_connsp_2 @ X22 @ X21 @ X20)
% 0.43/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.62          | ~ (l1_pre_topc @ X21)
% 0.43/0.62          | ~ (v2_pre_topc @ X21))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v2_pre_topc @ sk_A)
% 0.43/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.62          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.43/0.62          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.62          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.43/0.62          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      ((~ (l1_struct_0 @ sk_A)
% 0.43/0.62        | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.43/0.62        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '7'])).
% 0.43/0.62  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(dt_l1_pre_topc, axiom,
% 0.43/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.62  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.43/0.62        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)], ['8', '11'])).
% 0.43/0.62  thf('13', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['12', '13'])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      ((~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.43/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(dt_k1_pre_topc, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.43/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.62       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.43/0.62         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i]:
% 0.43/0.62         (~ (l1_pre_topc @ X13)
% 0.43/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.43/0.62          | (m1_pre_topc @ (k1_pre_topc @ X13 @ X14) @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('20', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.43/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.62  thf(d9_pre_topc, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( l1_pre_topc @ B ) =>
% 0.43/0.62           ( ( m1_pre_topc @ B @ A ) <=>
% 0.43/0.62             ( ( ![C:$i]:
% 0.43/0.62                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.43/0.62                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.43/0.62                     ( ?[D:$i]:
% 0.43/0.62                       ( ( m1_subset_1 @
% 0.43/0.62                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.43/0.62                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.43/0.62                         ( ( C ) =
% 0.43/0.62                           ( k9_subset_1 @
% 0.43/0.62                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.43/0.62               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.43/0.62  thf(zf_stmt_2, axiom,
% 0.43/0.62    (![D:$i,C:$i,B:$i,A:$i]:
% 0.43/0.62     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.43/0.62       ( ( ( C ) =
% 0.43/0.62           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.43/0.62         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.43/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_3, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( l1_pre_topc @ B ) =>
% 0.43/0.62           ( ( m1_pre_topc @ B @ A ) <=>
% 0.43/0.62             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.43/0.62               ( ![C:$i]:
% 0.43/0.62                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.43/0.62                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.43/0.62                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X8 : $i, X9 : $i]:
% 0.43/0.62         (~ (l1_pre_topc @ X8)
% 0.43/0.62          | ~ (m1_pre_topc @ X8 @ X9)
% 0.43/0.62          | (r1_tarski @ (k2_struct_0 @ X8) @ (k2_struct_0 @ X9))
% 0.43/0.62          | ~ (l1_pre_topc @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.43/0.62           (k2_struct_0 @ sk_A))
% 0.43/0.62        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.62  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.43/0.62         (k2_struct_0 @ sk_A))
% 0.43/0.62        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d10_pre_topc, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.43/0.62               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.43/0.62                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.43/0.62          | ((X2) != (k1_pre_topc @ X1 @ X0))
% 0.43/0.62          | ((k2_struct_0 @ X2) = (X0))
% 0.43/0.62          | ~ (m1_pre_topc @ X2 @ X1)
% 0.43/0.62          | ~ (v1_pre_topc @ X2)
% 0.43/0.62          | ~ (l1_pre_topc @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (l1_pre_topc @ X1)
% 0.43/0.62          | ~ (v1_pre_topc @ (k1_pre_topc @ X1 @ X0))
% 0.43/0.62          | ~ (m1_pre_topc @ (k1_pre_topc @ X1 @ X0) @ X1)
% 0.43/0.62          | ((k2_struct_0 @ (k1_pre_topc @ X1 @ X0)) = (X0))
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.43/0.62        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.43/0.62        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['25', '27'])).
% 0.43/0.62  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.43/0.62        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.43/0.62        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i]:
% 0.43/0.62         (~ (l1_pre_topc @ X13)
% 0.43/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.43/0.62          | (v1_pre_topc @ (k1_pre_topc @ X13 @ X14)))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)) | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('35', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.43/0.62        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['30', '35'])).
% 0.43/0.62  thf('37', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.43/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.62  thf('38', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.43/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.43/0.62  thf('39', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.43/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.62  thf(dt_m1_pre_topc, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) =>
% 0.43/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         (~ (m1_pre_topc @ X17 @ X18)
% 0.43/0.62          | (l1_pre_topc @ X17)
% 0.43/0.62          | ~ (l1_pre_topc @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.43/0.62  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('43', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['24', '38', '43'])).
% 0.43/0.62  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('47', plain, ($false),
% 0.43/0.62      inference('demod', [status(thm)], ['15', '44', '45', '46'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
