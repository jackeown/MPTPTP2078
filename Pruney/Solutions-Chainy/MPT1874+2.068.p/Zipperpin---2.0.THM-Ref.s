%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2ZIDH6FORH

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  90 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  455 (1353 expanded)
%              Number of equality atoms :   16 (  42 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
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

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X3 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ ( k2_pre_topc @ X14 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X3 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','31'])).

thf('33',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('34',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','34'])).

thf('36',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2ZIDH6FORH
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:44:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 37 iterations in 0.019s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(t42_tex_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v2_tex_2 @ B @ A ) =>
% 0.20/0.47             ( ![C:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47                 ( ( r2_hidden @ C @ B ) =>
% 0.20/0.47                   ( ( k9_subset_1 @
% 0.20/0.47                       ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.47                       ( k2_pre_topc @
% 0.20/0.47                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.47                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47              ( ( v2_tex_2 @ B @ A ) =>
% 0.20/0.47                ( ![C:$i]:
% 0.20/0.47                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47                    ( ( r2_hidden @ C @ B ) =>
% 0.20/0.47                      ( ( k9_subset_1 @
% 0.20/0.47                          ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.47                          ( k2_pre_topc @
% 0.20/0.47                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.47                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.20/0.47  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t5_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.47          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.47          | ~ (v1_xboole_0 @ X10)
% 0.20/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X11)
% 0.20/0.47          | ~ (m1_subset_1 @ X12 @ X11)
% 0.20/0.47          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.20/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.47         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.20/0.47         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.47          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.20/0.47          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.20/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(l3_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ X0 @ X2)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.47  thf(t63_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (k1_tarski @ X3) @ (k1_zfmisc_1 @ X4))
% 0.20/0.47          | ~ (r2_hidden @ X3 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.20/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t41_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.47             ( ![C:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47                 ( ( r1_tarski @ C @ B ) =>
% 0.20/0.47                   ( ( k9_subset_1 @
% 0.20/0.47                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.20/0.47                     ( C ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.47          | ~ (v2_tex_2 @ X13 @ X14)
% 0.20/0.47          | ~ (r1_tarski @ X15 @ X13)
% 0.20/0.47          | ((k9_subset_1 @ (u1_struct_0 @ X14) @ X13 @ 
% 0.20/0.47              (k2_pre_topc @ X14 @ X15)) = (X15))
% 0.20/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.47          | ~ (l1_pre_topc @ X14)
% 0.20/0.47          | ~ (v2_pre_topc @ X14)
% 0.20/0.47          | (v2_struct_0 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.47          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.47              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.20/0.47          | ~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.47          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.47          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.47              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.20/0.47          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.20/0.47        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.47            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.47  thf('24', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (k1_tarski @ X3) @ (k1_zfmisc_1 @ X4))
% 0.20/0.47          | ~ (r2_hidden @ X3 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf(t3_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.47  thf('28', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.47          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '28'])).
% 0.20/0.47  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.47         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))),
% 0.20/0.47      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((((k1_tarski @ sk_C_1) != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.20/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.20/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('34', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.47  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '34'])).
% 0.20/0.47  thf('36', plain, ($false), inference('sup-', [status(thm)], ['0', '35'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
