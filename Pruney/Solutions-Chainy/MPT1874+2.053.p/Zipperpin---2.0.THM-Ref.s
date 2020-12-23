%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u9cPHz9hql

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:48 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   69 (  98 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  498 (1402 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t42_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_tex_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k2_pre_topc @ X21 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('33',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','36'])).

thf('38',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('39',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','39'])).

thf('41',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u9cPHz9hql
% 0.13/0.37  % Computer   : n001.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 11:50:45 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 233 iterations in 0.133s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.62  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.38/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.62  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.62  thf(t42_tex_2, conjecture,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62           ( ( v2_tex_2 @ B @ A ) =>
% 0.38/0.62             ( ![C:$i]:
% 0.38/0.62               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62                 ( ( r2_hidden @ C @ B ) =>
% 0.38/0.62                   ( ( k9_subset_1 @
% 0.38/0.62                       ( u1_struct_0 @ A ) @ B @ 
% 0.38/0.62                       ( k2_pre_topc @
% 0.38/0.62                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.38/0.62                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i]:
% 0.38/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.62            ( l1_pre_topc @ A ) ) =>
% 0.38/0.62          ( ![B:$i]:
% 0.38/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62              ( ( v2_tex_2 @ B @ A ) =>
% 0.38/0.62                ( ![C:$i]:
% 0.38/0.62                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62                    ( ( r2_hidden @ C @ B ) =>
% 0.38/0.62                      ( ( k9_subset_1 @
% 0.38/0.62                          ( u1_struct_0 @ A ) @ B @ 
% 0.38/0.62                          ( k2_pre_topc @
% 0.38/0.62                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.38/0.62                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.38/0.62  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t5_subset, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X15 @ X16)
% 0.38/0.62          | ~ (v1_xboole_0 @ X17)
% 0.38/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(redefinition_k6_domain_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.62       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X18 : $i, X19 : $i]:
% 0.38/0.62         ((v1_xboole_0 @ X18)
% 0.38/0.62          | ~ (m1_subset_1 @ X19 @ X18)
% 0.38/0.62          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.38/0.62         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.38/0.62          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.62  thf('9', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t3_subset, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X12 : $i, X13 : $i]:
% 0.38/0.62         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.62  thf('12', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf(t28_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X6 : $i, X7 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('14', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf(d4_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.38/0.62       ( ![D:$i]:
% 0.38/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.62           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.62          | (r2_hidden @ X4 @ X2)
% 0.38/0.62          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.62         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['14', '16'])).
% 0.38/0.62  thf('18', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['9', '17'])).
% 0.38/0.62  thf(l1_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X9 : $i, X11 : $i]:
% 0.38/0.62         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 0.38/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.62  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X12 : $i, X14 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t41_tex_2, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62           ( ( v2_tex_2 @ B @ A ) <=>
% 0.38/0.62             ( ![C:$i]:
% 0.38/0.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62                 ( ( r1_tarski @ C @ B ) =>
% 0.38/0.62                   ( ( k9_subset_1 @
% 0.38/0.62                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.38/0.62                     ( C ) ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.38/0.62          | ~ (v2_tex_2 @ X20 @ X21)
% 0.38/0.62          | ~ (r1_tarski @ X22 @ X20)
% 0.38/0.62          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 0.38/0.62              (k2_pre_topc @ X21 @ X22)) = (X22))
% 0.38/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.38/0.62          | ~ (l1_pre_topc @ X21)
% 0.38/0.62          | ~ (v2_pre_topc @ X21)
% 0.38/0.62          | (v2_struct_0 @ X21))),
% 0.38/0.62      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v2_struct_0 @ sk_A)
% 0.38/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.62          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.38/0.62          | ~ (r1_tarski @ X0 @ sk_B)
% 0.38/0.62          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.62  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('28', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v2_struct_0 @ sk_A)
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.62          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.38/0.62          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.38/0.62        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['22', '29'])).
% 0.38/0.62  thf('31', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X9 : $i, X11 : $i]:
% 0.38/0.62         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 0.38/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.62  thf('33', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.38/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['30', '33'])).
% 0.38/0.62  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))),
% 0.38/0.62      inference('clc', [status(thm)], ['34', '35'])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      ((((k1_tarski @ sk_C_1) != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['8', '36'])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.62  thf('39', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['37', '38'])).
% 0.38/0.62  thf('40', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.38/0.62      inference('demod', [status(thm)], ['3', '39'])).
% 0.38/0.62  thf('41', plain, ($false), inference('sup-', [status(thm)], ['0', '40'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
