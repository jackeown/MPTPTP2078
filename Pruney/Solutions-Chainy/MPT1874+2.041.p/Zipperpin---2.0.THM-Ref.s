%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I5mG6bEejt

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 135 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  542 (1674 expanded)
%              Number of equality atoms :   16 (  49 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( ( k6_domain_1 @ X41 @ X42 )
        = ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ~ ( r1_tarski @ X45 @ X43 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X44 ) @ X43 @ ( k2_pre_topc @ X44 @ X45 ) )
        = X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( m1_subset_1 @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X32 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('26',plain,(
    ! [X31: $i] :
      ( ( k2_subset_1 @ X31 )
      = X31 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ X28 @ X29 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(clc,[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['23','30'])).

thf('35',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( ( k6_domain_1 @ X41 @ X42 )
        = ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('36',plain,
    ( ( ( k6_domain_1 @ sk_B @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k6_domain_1 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','45'])).

thf('47',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','47'])).

thf('49',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I5mG6bEejt
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 175 iterations in 0.062s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.54  thf(t42_tex_2, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v2_tex_2 @ B @ A ) =>
% 0.22/0.54             ( ![C:$i]:
% 0.22/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.54                 ( ( r2_hidden @ C @ B ) =>
% 0.22/0.54                   ( ( k9_subset_1 @
% 0.22/0.54                       ( u1_struct_0 @ A ) @ B @ 
% 0.22/0.54                       ( k2_pre_topc @
% 0.22/0.54                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.22/0.54                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.54            ( l1_pre_topc @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54              ( ( v2_tex_2 @ B @ A ) =>
% 0.22/0.54                ( ![C:$i]:
% 0.22/0.54                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.54                    ( ( r2_hidden @ C @ B ) =>
% 0.22/0.54                      ( ( k9_subset_1 @
% 0.22/0.54                          ( u1_struct_0 @ A ) @ B @ 
% 0.22/0.54                          ( k2_pre_topc @
% 0.22/0.54                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.22/0.54                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.22/0.54  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t5_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X36 @ X37)
% 0.22/0.54          | ~ (v1_xboole_0 @ X38)
% 0.22/0.54          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X41 : $i, X42 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ X41)
% 0.22/0.54          | ~ (m1_subset_1 @ X42 @ X41)
% 0.22/0.54          | ((k6_domain_1 @ X41 @ X42) = (k1_tarski @ X42)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.54  thf('7', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_k6_domain_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.54       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X39 : $i, X40 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ X39)
% 0.22/0.54          | ~ (m1_subset_1 @ X40 @ X39)
% 0.22/0.54          | (m1_subset_1 @ (k6_domain_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.22/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t41_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v2_tex_2 @ B @ A ) <=>
% 0.22/0.54             ( ![C:$i]:
% 0.22/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54                 ( ( r1_tarski @ C @ B ) =>
% 0.22/0.54                   ( ( k9_subset_1 @
% 0.22/0.54                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.22/0.54                     ( C ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.22/0.54          | ~ (v2_tex_2 @ X43 @ X44)
% 0.22/0.54          | ~ (r1_tarski @ X45 @ X43)
% 0.22/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X44) @ X43 @ 
% 0.22/0.54              (k2_pre_topc @ X44 @ X45)) = (X45))
% 0.22/0.54          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.22/0.54          | ~ (l1_pre_topc @ X44)
% 0.22/0.54          | ~ (v2_pre_topc @ X44)
% 0.22/0.54          | (v2_struct_0 @ X44))),
% 0.22/0.54      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_A)
% 0.22/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.54              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.54          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('15', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.54              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | ~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B)
% 0.22/0.54        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.54            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.22/0.54            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.22/0.54        | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['9', '16'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.54         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.22/0.54         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | ~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B)
% 0.22/0.54        | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      ((~ (r1_tarski @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_B)
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '21'])).
% 0.22/0.54  thf('23', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d2_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X28 : $i, X29 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X28 @ X29)
% 0.22/0.54          | (m1_subset_1 @ X28 @ X29)
% 0.22/0.54          | (v1_xboole_0 @ X29))),
% 0.22/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.54  thf(dt_k2_subset_1, axiom,
% 0.22/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X32 : $i]: (m1_subset_1 @ (k2_subset_1 @ X32) @ (k1_zfmisc_1 @ X32))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.54  thf('26', plain, (![X31 : $i]: ((k2_subset_1 @ X31) = (X31))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.54  thf('27', plain, (![X32 : $i]: (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X32))),
% 0.22/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X36 @ X37)
% 0.22/0.54          | ~ (v1_xboole_0 @ X38)
% 0.22/0.54          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X28 : $i, X29 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X28 @ X29) | ~ (r2_hidden @ X28 @ X29))),
% 0.22/0.54      inference('clc', [status(thm)], ['24', '29'])).
% 0.22/0.54  thf('31', plain, ((m1_subset_1 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['23', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X39 : $i, X40 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ X39)
% 0.22/0.54          | ~ (m1_subset_1 @ X40 @ X39)
% 0.22/0.54          | (m1_subset_1 @ (k6_domain_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (((m1_subset_1 @ (k6_domain_1 @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))
% 0.22/0.54        | (v1_xboole_0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.54  thf('34', plain, ((m1_subset_1 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['23', '30'])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X41 : $i, X42 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ X41)
% 0.22/0.54          | ~ (m1_subset_1 @ X42 @ X41)
% 0.22/0.54          | ((k6_domain_1 @ X41 @ X42) = (k1_tarski @ X42)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      ((((k6_domain_1 @ sk_B @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.22/0.54        | (v1_xboole_0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.54  thf('37', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.54  thf('39', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.54  thf('40', plain, (((k6_domain_1 @ sk_B @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.22/0.54      inference('clc', [status(thm)], ['36', '39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))
% 0.22/0.54        | (v1_xboole_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '40'])).
% 0.22/0.54  thf('42', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.54      inference('clc', [status(thm)], ['41', '42'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X33 : $i, X34 : $i]:
% 0.22/0.54         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('45', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['22', '45'])).
% 0.22/0.54  thf('47', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.54  thf('48', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '47'])).
% 0.22/0.54  thf('49', plain, ($false), inference('sup-', [status(thm)], ['0', '48'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
