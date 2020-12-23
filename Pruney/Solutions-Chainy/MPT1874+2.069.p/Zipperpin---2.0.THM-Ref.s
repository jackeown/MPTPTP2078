%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JY0VYTQTe

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:50 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   61 (  87 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  468 (1294 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ ( k2_pre_topc @ X13 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( ( k6_domain_1 @ X10 @ X11 )
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('33',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','33'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JY0VYTQTe
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:31:34 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 54 iterations in 0.023s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.48  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.23/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.48  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.23/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.48  thf(t42_tex_2, conjecture,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ( v2_tex_2 @ B @ A ) =>
% 0.23/0.48             ( ![C:$i]:
% 0.23/0.48               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.48                 ( ( r2_hidden @ C @ B ) =>
% 0.23/0.48                   ( ( k9_subset_1 @
% 0.23/0.48                       ( u1_struct_0 @ A ) @ B @ 
% 0.23/0.48                       ( k2_pre_topc @
% 0.23/0.48                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.23/0.48                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i]:
% 0.23/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.48            ( l1_pre_topc @ A ) ) =>
% 0.23/0.48          ( ![B:$i]:
% 0.23/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48              ( ( v2_tex_2 @ B @ A ) =>
% 0.23/0.48                ( ![C:$i]:
% 0.23/0.48                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.48                    ( ( r2_hidden @ C @ B ) =>
% 0.23/0.48                      ( ( k9_subset_1 @
% 0.23/0.48                          ( u1_struct_0 @ A ) @ B @ 
% 0.23/0.48                          ( k2_pre_topc @
% 0.23/0.48                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.23/0.48                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.23/0.48  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t5_subset, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i]:
% 0.23/0.48     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.23/0.48          ( v1_xboole_0 @ C ) ) ))).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.48         (~ (r2_hidden @ X7 @ X8)
% 0.23/0.48          | ~ (v1_xboole_0 @ X9)
% 0.23/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.23/0.48      inference('cnf', [status(esa)], [t5_subset])).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.23/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.48  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t2_subset, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.23/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.48  thf('5', plain,
% 0.23/0.48      (![X2 : $i, X3 : $i]:
% 0.23/0.48         ((r2_hidden @ X2 @ X3)
% 0.23/0.48          | (v1_xboole_0 @ X3)
% 0.23/0.48          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.23/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.48  thf('6', plain,
% 0.23/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.48        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.48  thf(t63_subset_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( r2_hidden @ A @ B ) =>
% 0.23/0.48       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.23/0.48  thf('7', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i]:
% 0.23/0.48         ((m1_subset_1 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X1))
% 0.23/0.48          | ~ (r2_hidden @ X0 @ X1))),
% 0.23/0.48      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.23/0.48  thf('8', plain,
% 0.23/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.48        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.23/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.48  thf('9', plain,
% 0.23/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t41_tex_2, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ( v2_tex_2 @ B @ A ) <=>
% 0.23/0.48             ( ![C:$i]:
% 0.23/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48                 ( ( r1_tarski @ C @ B ) =>
% 0.23/0.48                   ( ( k9_subset_1 @
% 0.23/0.48                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.23/0.48                     ( C ) ) ) ) ) ) ) ) ))).
% 0.23/0.48  thf('10', plain,
% 0.23/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.23/0.48          | ~ (v2_tex_2 @ X12 @ X13)
% 0.23/0.48          | ~ (r1_tarski @ X14 @ X12)
% 0.23/0.48          | ((k9_subset_1 @ (u1_struct_0 @ X13) @ X12 @ 
% 0.23/0.48              (k2_pre_topc @ X13 @ X14)) = (X14))
% 0.23/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.23/0.48          | ~ (l1_pre_topc @ X13)
% 0.23/0.48          | ~ (v2_pre_topc @ X13)
% 0.23/0.48          | (v2_struct_0 @ X13))),
% 0.23/0.48      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.23/0.48  thf('11', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((v2_struct_0 @ sk_A)
% 0.23/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.48          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.23/0.48              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.23/0.48          | ~ (r1_tarski @ X0 @ sk_B)
% 0.23/0.48          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.48  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('14', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('15', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((v2_struct_0 @ sk_A)
% 0.23/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.48          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.23/0.48              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.23/0.48          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.23/0.48      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.23/0.48  thf('16', plain,
% 0.23/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.48        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.23/0.48        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.23/0.48            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.23/0.48        | (v2_struct_0 @ sk_A))),
% 0.23/0.48      inference('sup-', [status(thm)], ['8', '15'])).
% 0.23/0.48  thf('17', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('18', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i]:
% 0.23/0.48         ((m1_subset_1 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X1))
% 0.23/0.48          | ~ (r2_hidden @ X0 @ X1))),
% 0.23/0.48      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.23/0.48  thf('19', plain,
% 0.23/0.48      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.23/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.48  thf(t3_subset, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.48  thf('20', plain,
% 0.23/0.48      (![X4 : $i, X5 : $i]:
% 0.23/0.48         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.48  thf('21', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.23/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.48  thf('22', plain,
% 0.23/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.48        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.23/0.48            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.23/0.48        | (v2_struct_0 @ sk_A))),
% 0.23/0.48      inference('demod', [status(thm)], ['16', '21'])).
% 0.23/0.48  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('24', plain,
% 0.23/0.48      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.23/0.48          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.23/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.48  thf('25', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.23/0.48  thf('26', plain,
% 0.23/0.48      (![X10 : $i, X11 : $i]:
% 0.23/0.48         ((v1_xboole_0 @ X10)
% 0.23/0.48          | ~ (m1_subset_1 @ X11 @ X10)
% 0.23/0.48          | ((k6_domain_1 @ X10 @ X11) = (k1_tarski @ X11)))),
% 0.23/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.48  thf('27', plain,
% 0.23/0.48      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.23/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.48  thf('28', plain,
% 0.23/0.48      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.23/0.48         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.23/0.48         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('29', plain,
% 0.23/0.48      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.23/0.48          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.23/0.48          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.23/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.48  thf('30', plain,
% 0.23/0.48      ((((k1_tarski @ sk_C_1) != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.23/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['24', '29'])).
% 0.23/0.48  thf('31', plain,
% 0.23/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.48        | ((k1_tarski @ sk_C_1)
% 0.23/0.48            != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.23/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.23/0.48  thf('32', plain,
% 0.23/0.48      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.23/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.48  thf('33', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.23/0.48  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.23/0.48      inference('demod', [status(thm)], ['3', '33'])).
% 0.23/0.48  thf('35', plain, ($false), inference('sup-', [status(thm)], ['0', '34'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
