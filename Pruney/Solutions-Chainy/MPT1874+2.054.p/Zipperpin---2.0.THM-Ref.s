%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nrWLZceWMT

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:48 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 106 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  544 (1457 expanded)
%              Number of equality atoms :   25 (  52 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['12','15'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X9 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tex_2 @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ ( k2_pre_topc @ X22 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X9 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','40'])).

thf('42',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('43',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','43'])).

thf('45',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nrWLZceWMT
% 0.16/0.36  % Computer   : n010.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 14:48:30 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.23/0.37  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 152 iterations in 0.091s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.56  thf(t42_tex_2, conjecture,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56           ( ( v2_tex_2 @ B @ A ) =>
% 0.39/0.56             ( ![C:$i]:
% 0.39/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.56                 ( ( r2_hidden @ C @ B ) =>
% 0.39/0.56                   ( ( k9_subset_1 @
% 0.39/0.56                       ( u1_struct_0 @ A ) @ B @ 
% 0.39/0.56                       ( k2_pre_topc @
% 0.39/0.56                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.39/0.56                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i]:
% 0.39/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.56            ( l1_pre_topc @ A ) ) =>
% 0.39/0.56          ( ![B:$i]:
% 0.39/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56              ( ( v2_tex_2 @ B @ A ) =>
% 0.39/0.56                ( ![C:$i]:
% 0.39/0.56                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.56                    ( ( r2_hidden @ C @ B ) =>
% 0.39/0.56                      ( ( k9_subset_1 @
% 0.39/0.56                          ( u1_struct_0 @ A ) @ B @ 
% 0.39/0.56                          ( k2_pre_topc @
% 0.39/0.56                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.39/0.56                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.39/0.56  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t5_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.39/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X16 @ X17)
% 0.39/0.56          | ~ (v1_xboole_0 @ X18)
% 0.39/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.56  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X19 : $i, X20 : $i]:
% 0.39/0.56         ((v1_xboole_0 @ X19)
% 0.39/0.56          | ~ (m1_subset_1 @ X20 @ X19)
% 0.39/0.56          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.56         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.39/0.56         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.56          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.39/0.56          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('9', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t3_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X13 : $i, X14 : $i]:
% 0.39/0.56         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.56  thf('12', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.56  thf(t28_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i]:
% 0.39/0.56         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.56  thf(t12_setfam_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i]:
% 0.39/0.56         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.39/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i]:
% 0.39/0.56         (((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (X6))
% 0.39/0.56          | ~ (r1_tarski @ X6 @ X7))),
% 0.39/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['12', '15'])).
% 0.39/0.56  thf(d4_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.39/0.56       ( ![D:$i]:
% 0.39/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.39/0.56          | (r2_hidden @ X4 @ X2)
% 0.39/0.56          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.39/0.56         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i]:
% 0.39/0.56         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.39/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.39/0.56         ((r2_hidden @ X4 @ X2)
% 0.39/0.56          | ~ (r2_hidden @ X4 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 0.39/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['16', '20'])).
% 0.39/0.56  thf('22', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['9', '21'])).
% 0.39/0.56  thf(t63_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.56       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         ((m1_subset_1 @ (k1_tarski @ X9) @ (k1_zfmisc_1 @ X10))
% 0.39/0.56          | ~ (r2_hidden @ X9 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.39/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.56  thf('25', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t41_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56           ( ( v2_tex_2 @ B @ A ) <=>
% 0.39/0.56             ( ![C:$i]:
% 0.39/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56                 ( ( r1_tarski @ C @ B ) =>
% 0.39/0.56                   ( ( k9_subset_1 @
% 0.39/0.56                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.39/0.56                     ( C ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf('26', plain,
% 0.39/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.39/0.56          | ~ (v2_tex_2 @ X21 @ X22)
% 0.39/0.56          | ~ (r1_tarski @ X23 @ X21)
% 0.39/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ 
% 0.39/0.56              (k2_pre_topc @ X22 @ X23)) = (X23))
% 0.39/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.39/0.56          | ~ (l1_pre_topc @ X22)
% 0.39/0.56          | ~ (v2_pre_topc @ X22)
% 0.39/0.56          | (v2_struct_0 @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_A)
% 0.39/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.56              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.39/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.56          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.56  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('30', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('31', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_A)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.56              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.39/0.56          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.39/0.56      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.39/0.56  thf('32', plain,
% 0.39/0.56      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.39/0.56        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.56            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.39/0.56        | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['24', '31'])).
% 0.39/0.56  thf('33', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('34', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         ((m1_subset_1 @ (k1_tarski @ X9) @ (k1_zfmisc_1 @ X10))
% 0.39/0.56          | ~ (r2_hidden @ X9 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.39/0.56  thf('35', plain,
% 0.39/0.56      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.56  thf('36', plain,
% 0.39/0.56      (![X13 : $i, X14 : $i]:
% 0.39/0.56         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.56  thf('37', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.39/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.56          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.39/0.56        | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['32', '37'])).
% 0.39/0.56  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('40', plain,
% 0.39/0.56      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.56         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))),
% 0.39/0.56      inference('clc', [status(thm)], ['38', '39'])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      ((((k1_tarski @ sk_C_1) != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['8', '40'])).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('43', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('clc', [status(thm)], ['41', '42'])).
% 0.39/0.56  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.39/0.56      inference('demod', [status(thm)], ['3', '43'])).
% 0.39/0.56  thf('45', plain, ($false), inference('sup-', [status(thm)], ['0', '44'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
