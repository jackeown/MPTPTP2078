%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y6WdZnvRX5

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:09 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 115 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  637 (1546 expanded)
%              Number of equality atoms :   39 (  72 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k3_xboole_0 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('34',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_hidden @ ( sk_D @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_C )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_C )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('37',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('40',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','25','42','43'])).

thf('45',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('47',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y6WdZnvRX5
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:26:08 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.82/2.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.82/2.01  % Solved by: fo/fo7.sh
% 1.82/2.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.82/2.01  % done 1525 iterations in 1.548s
% 1.82/2.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.82/2.01  % SZS output start Refutation
% 1.82/2.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.82/2.01  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.82/2.01  thf(sk_C_type, type, sk_C: $i).
% 1.82/2.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.82/2.01  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.82/2.01  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.82/2.01  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.82/2.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.82/2.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.82/2.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.82/2.01  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.82/2.01  thf(sk_B_type, type, sk_B: $i).
% 1.82/2.01  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.82/2.01  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.82/2.01  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.82/2.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.82/2.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.82/2.01  thf(sk_A_type, type, sk_A: $i).
% 1.82/2.01  thf(d3_struct_0, axiom,
% 1.82/2.01    (![A:$i]:
% 1.82/2.01     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.82/2.01  thf('0', plain,
% 1.82/2.01      (![X16 : $i]:
% 1.82/2.01         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 1.82/2.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.01  thf(t81_tops_1, conjecture,
% 1.82/2.01    (![A:$i]:
% 1.82/2.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.82/2.01       ( ![B:$i]:
% 1.82/2.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.82/2.01           ( ( v1_tops_1 @ B @ A ) =>
% 1.82/2.01             ( ![C:$i]:
% 1.82/2.01               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.82/2.01                 ( ( v3_pre_topc @ C @ A ) =>
% 1.82/2.01                   ( ( k2_pre_topc @ A @ C ) =
% 1.82/2.01                     ( k2_pre_topc @
% 1.82/2.01                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 1.82/2.01  thf(zf_stmt_0, negated_conjecture,
% 1.82/2.01    (~( ![A:$i]:
% 1.82/2.01        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.82/2.01          ( ![B:$i]:
% 1.82/2.01            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.82/2.01              ( ( v1_tops_1 @ B @ A ) =>
% 1.82/2.01                ( ![C:$i]:
% 1.82/2.01                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.82/2.01                    ( ( v3_pre_topc @ C @ A ) =>
% 1.82/2.01                      ( ( k2_pre_topc @ A @ C ) =
% 1.82/2.01                        ( k2_pre_topc @
% 1.82/2.01                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 1.82/2.01    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 1.82/2.01  thf('1', plain,
% 1.82/2.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf('2', plain,
% 1.82/2.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf(t41_tops_1, axiom,
% 1.82/2.01    (![A:$i]:
% 1.82/2.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.82/2.01       ( ![B:$i]:
% 1.82/2.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.82/2.01           ( ![C:$i]:
% 1.82/2.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.82/2.01               ( ( v3_pre_topc @ B @ A ) =>
% 1.82/2.01                 ( ( k2_pre_topc @
% 1.82/2.01                     A @ 
% 1.82/2.01                     ( k9_subset_1 @
% 1.82/2.01                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 1.82/2.01                   ( k2_pre_topc @
% 1.82/2.01                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 1.82/2.01  thf('3', plain,
% 1.82/2.01      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.82/2.01         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.82/2.01          | ~ (v3_pre_topc @ X20 @ X21)
% 1.82/2.01          | ((k2_pre_topc @ X21 @ 
% 1.82/2.01              (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 1.82/2.01               (k2_pre_topc @ X21 @ X22)))
% 1.82/2.01              = (k2_pre_topc @ X21 @ 
% 1.82/2.01                 (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X22)))
% 1.82/2.01          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.82/2.01          | ~ (l1_pre_topc @ X21)
% 1.82/2.01          | ~ (v2_pre_topc @ X21))),
% 1.82/2.01      inference('cnf', [status(esa)], [t41_tops_1])).
% 1.82/2.01  thf('4', plain,
% 1.82/2.01      (![X0 : $i]:
% 1.82/2.01         (~ (v2_pre_topc @ sk_A)
% 1.82/2.01          | ~ (l1_pre_topc @ sk_A)
% 1.82/2.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.82/2.01          | ((k2_pre_topc @ sk_A @ 
% 1.82/2.01              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.82/2.01               (k2_pre_topc @ sk_A @ X0)))
% 1.82/2.01              = (k2_pre_topc @ sk_A @ 
% 1.82/2.01                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))
% 1.82/2.01          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 1.82/2.01      inference('sup-', [status(thm)], ['2', '3'])).
% 1.82/2.01  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf('7', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf('8', plain,
% 1.82/2.01      (![X0 : $i]:
% 1.82/2.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.82/2.01          | ((k2_pre_topc @ sk_A @ 
% 1.82/2.01              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.82/2.01               (k2_pre_topc @ sk_A @ X0)))
% 1.82/2.01              = (k2_pre_topc @ sk_A @ 
% 1.82/2.01                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 1.82/2.01      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.82/2.01  thf('9', plain,
% 1.82/2.01      (((k2_pre_topc @ sk_A @ 
% 1.82/2.01         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.82/2.01          (k2_pre_topc @ sk_A @ sk_B)))
% 1.82/2.01         = (k2_pre_topc @ sk_A @ 
% 1.82/2.01            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 1.82/2.01      inference('sup-', [status(thm)], ['1', '8'])).
% 1.82/2.01  thf('10', plain,
% 1.82/2.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf(d3_tops_1, axiom,
% 1.82/2.01    (![A:$i]:
% 1.82/2.01     ( ( l1_pre_topc @ A ) =>
% 1.82/2.01       ( ![B:$i]:
% 1.82/2.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.82/2.01           ( ( v1_tops_1 @ B @ A ) <=>
% 1.82/2.01             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 1.82/2.01  thf('11', plain,
% 1.82/2.01      (![X18 : $i, X19 : $i]:
% 1.82/2.01         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.82/2.01          | ~ (v1_tops_1 @ X18 @ X19)
% 1.82/2.01          | ((k2_pre_topc @ X19 @ X18) = (k2_struct_0 @ X19))
% 1.82/2.01          | ~ (l1_pre_topc @ X19))),
% 1.82/2.01      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.82/2.01  thf('12', plain,
% 1.82/2.01      ((~ (l1_pre_topc @ sk_A)
% 1.82/2.01        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 1.82/2.01        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 1.82/2.01      inference('sup-', [status(thm)], ['10', '11'])).
% 1.82/2.01  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf('14', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf('15', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 1.82/2.01      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.82/2.01  thf('16', plain,
% 1.82/2.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf(redefinition_k9_subset_1, axiom,
% 1.82/2.01    (![A:$i,B:$i,C:$i]:
% 1.82/2.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.82/2.01       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.82/2.01  thf('17', plain,
% 1.82/2.01      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.82/2.01         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 1.82/2.01          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.82/2.01      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.82/2.01  thf('18', plain,
% 1.82/2.01      (![X0 : $i]:
% 1.82/2.01         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.82/2.01           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.82/2.01      inference('sup-', [status(thm)], ['16', '17'])).
% 1.82/2.01  thf('19', plain,
% 1.82/2.01      (((k2_pre_topc @ sk_A @ 
% 1.82/2.01         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ (k2_struct_0 @ sk_A)))
% 1.82/2.01         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 1.82/2.01      inference('demod', [status(thm)], ['9', '15', '18'])).
% 1.82/2.01  thf('20', plain,
% 1.82/2.01      ((((k2_pre_topc @ sk_A @ 
% 1.82/2.01          (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C @ (k2_struct_0 @ sk_A)))
% 1.82/2.01          = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))
% 1.82/2.01        | ~ (l1_struct_0 @ sk_A))),
% 1.82/2.01      inference('sup+', [status(thm)], ['0', '19'])).
% 1.82/2.01  thf(dt_k2_subset_1, axiom,
% 1.82/2.01    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.82/2.01  thf('21', plain,
% 1.82/2.01      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 1.82/2.01      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.82/2.01  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.82/2.01  thf('22', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 1.82/2.01      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.82/2.01  thf('23', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 1.82/2.01      inference('demod', [status(thm)], ['21', '22'])).
% 1.82/2.01  thf('24', plain,
% 1.82/2.01      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.82/2.01         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 1.82/2.01          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.82/2.01      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.82/2.01  thf('25', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 1.82/2.01      inference('sup-', [status(thm)], ['23', '24'])).
% 1.82/2.01  thf('26', plain,
% 1.82/2.01      (![X16 : $i]:
% 1.82/2.01         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 1.82/2.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.82/2.01  thf(d4_xboole_0, axiom,
% 1.82/2.01    (![A:$i,B:$i,C:$i]:
% 1.82/2.01     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.82/2.01       ( ![D:$i]:
% 1.82/2.01         ( ( r2_hidden @ D @ C ) <=>
% 1.82/2.01           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.82/2.01  thf('27', plain,
% 1.82/2.01      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.82/2.01         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.82/2.01          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.82/2.01          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.82/2.01      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.82/2.01  thf('28', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.82/2.01          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.82/2.01      inference('eq_fact', [status(thm)], ['27'])).
% 1.82/2.01  thf('29', plain,
% 1.82/2.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf(l3_subset_1, axiom,
% 1.82/2.01    (![A:$i,B:$i]:
% 1.82/2.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.82/2.01       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.82/2.01  thf('30', plain,
% 1.82/2.01      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.82/2.01         (~ (r2_hidden @ X8 @ X9)
% 1.82/2.01          | (r2_hidden @ X8 @ X10)
% 1.82/2.01          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.82/2.01      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.82/2.01  thf('31', plain,
% 1.82/2.01      (![X0 : $i]:
% 1.82/2.01         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 1.82/2.01      inference('sup-', [status(thm)], ['29', '30'])).
% 1.82/2.01  thf('32', plain,
% 1.82/2.01      (![X0 : $i]:
% 1.82/2.01         (((sk_C) = (k3_xboole_0 @ sk_C @ X0))
% 1.82/2.01          | (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 1.82/2.01      inference('sup-', [status(thm)], ['28', '31'])).
% 1.82/2.01  thf('33', plain,
% 1.82/2.01      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.82/2.01         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.82/2.01          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.82/2.01          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.82/2.01          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.82/2.01      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.82/2.01  thf('34', plain,
% 1.82/2.01      ((((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))
% 1.82/2.01        | ~ (r2_hidden @ (sk_D @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_C)
% 1.82/2.01        | ~ (r2_hidden @ (sk_D @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_C)
% 1.82/2.01        | ((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 1.82/2.01      inference('sup-', [status(thm)], ['32', '33'])).
% 1.82/2.01  thf('35', plain,
% 1.82/2.01      ((~ (r2_hidden @ (sk_D @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_C)
% 1.82/2.01        | ((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 1.82/2.01      inference('simplify', [status(thm)], ['34'])).
% 1.82/2.01  thf('36', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.82/2.01          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.82/2.01      inference('eq_fact', [status(thm)], ['27'])).
% 1.82/2.01  thf('37', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.82/2.01      inference('clc', [status(thm)], ['35', '36'])).
% 1.82/2.01  thf('38', plain,
% 1.82/2.01      ((((sk_C) = (k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)))
% 1.82/2.01        | ~ (l1_struct_0 @ sk_A))),
% 1.82/2.01      inference('sup+', [status(thm)], ['26', '37'])).
% 1.82/2.01  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf(dt_l1_pre_topc, axiom,
% 1.82/2.01    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.82/2.01  thf('40', plain,
% 1.82/2.01      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 1.82/2.01      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.82/2.01  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 1.82/2.01      inference('sup-', [status(thm)], ['39', '40'])).
% 1.82/2.01  thf('42', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 1.82/2.01      inference('demod', [status(thm)], ['38', '41'])).
% 1.82/2.01  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 1.82/2.01      inference('sup-', [status(thm)], ['39', '40'])).
% 1.82/2.01  thf('44', plain,
% 1.82/2.01      (((k2_pre_topc @ sk_A @ sk_C)
% 1.82/2.01         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 1.82/2.01      inference('demod', [status(thm)], ['20', '25', '42', '43'])).
% 1.82/2.01  thf('45', plain,
% 1.82/2.01      (((k2_pre_topc @ sk_A @ sk_C)
% 1.82/2.01         != (k2_pre_topc @ sk_A @ 
% 1.82/2.01             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf('46', plain,
% 1.82/2.01      (![X0 : $i]:
% 1.82/2.01         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.82/2.01           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.82/2.01      inference('sup-', [status(thm)], ['16', '17'])).
% 1.82/2.01  thf('47', plain,
% 1.82/2.01      (((k2_pre_topc @ sk_A @ sk_C)
% 1.82/2.01         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 1.82/2.01      inference('demod', [status(thm)], ['45', '46'])).
% 1.82/2.01  thf('48', plain, ($false),
% 1.82/2.01      inference('simplify_reflect-', [status(thm)], ['44', '47'])).
% 1.82/2.01  
% 1.82/2.01  % SZS output end Refutation
% 1.82/2.01  
% 1.82/2.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
