%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kPmrXzoWlS

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 119 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  562 (1744 expanded)
%              Number of equality atoms :   21 (  56 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ ( k2_pre_topc @ X16 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k6_domain_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('41',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('46',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','46'])).

thf('48',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kPmrXzoWlS
% 0.16/0.37  % Computer   : n024.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 18:50:36 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 95 iterations in 0.056s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.23/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.23/0.54  thf(t42_tex_2, conjecture,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54           ( ( v2_tex_2 @ B @ A ) =>
% 0.23/0.54             ( ![C:$i]:
% 0.23/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54                 ( ( r2_hidden @ C @ B ) =>
% 0.23/0.54                   ( ( k9_subset_1 @
% 0.23/0.54                       ( u1_struct_0 @ A ) @ B @ 
% 0.23/0.54                       ( k2_pre_topc @
% 0.23/0.54                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.23/0.54                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i]:
% 0.23/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.54            ( l1_pre_topc @ A ) ) =>
% 0.23/0.54          ( ![B:$i]:
% 0.23/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54              ( ( v2_tex_2 @ B @ A ) =>
% 0.23/0.54                ( ![C:$i]:
% 0.23/0.54                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54                    ( ( r2_hidden @ C @ B ) =>
% 0.23/0.54                      ( ( k9_subset_1 @
% 0.23/0.54                          ( u1_struct_0 @ A ) @ B @ 
% 0.23/0.54                          ( k2_pre_topc @
% 0.23/0.54                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.23/0.54                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.23/0.54  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(t5_subset, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.23/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X8 @ X9)
% 0.23/0.54          | ~ (v1_xboole_0 @ X10)
% 0.23/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.54  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      (![X13 : $i, X14 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X13)
% 0.23/0.54          | ~ (m1_subset_1 @ X14 @ X13)
% 0.23/0.54          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.54  thf('7', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(dt_k6_domain_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.54       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X11 : $i, X12 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X11)
% 0.23/0.54          | ~ (m1_subset_1 @ X12 @ X11)
% 0.23/0.54          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.23/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.23/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup+', [status(thm)], ['6', '9'])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.23/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.54      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(t41_tex_2, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54           ( ( v2_tex_2 @ B @ A ) <=>
% 0.23/0.54             ( ![C:$i]:
% 0.23/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54                 ( ( r1_tarski @ C @ B ) =>
% 0.23/0.54                   ( ( k9_subset_1 @
% 0.23/0.54                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.23/0.54                     ( C ) ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.23/0.54          | ~ (v2_tex_2 @ X15 @ X16)
% 0.23/0.54          | ~ (r1_tarski @ X17 @ X15)
% 0.23/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ 
% 0.23/0.54              (k2_pre_topc @ X16 @ X17)) = (X17))
% 0.23/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.23/0.54          | ~ (l1_pre_topc @ X16)
% 0.23/0.54          | ~ (v2_pre_topc @ X16)
% 0.23/0.54          | (v2_struct_0 @ X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((v2_struct_0 @ sk_A)
% 0.23/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.23/0.54              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.23/0.54          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.23/0.54          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.54  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('17', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((v2_struct_0 @ sk_A)
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.23/0.54              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.23/0.54          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.23/0.54      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)
% 0.23/0.54        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.23/0.54            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.23/0.54        | (v2_struct_0 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['11', '18'])).
% 0.23/0.54  thf('20', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(t1_subset, axiom,
% 0.23/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.23/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.23/0.54  thf('22', plain, ((m1_subset_1 @ sk_C_1 @ sk_B_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      (![X11 : $i, X12 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X11)
% 0.23/0.54          | ~ (m1_subset_1 @ X12 @ X11)
% 0.23/0.54          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.23/0.54  thf('24', plain,
% 0.23/0.54      (((m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))
% 0.23/0.54        | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.54  thf('25', plain, ((m1_subset_1 @ sk_C_1 @ sk_B_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      (![X13 : $i, X14 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X13)
% 0.23/0.54          | ~ (m1_subset_1 @ X14 @ X13)
% 0.23/0.54          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      ((((k6_domain_1 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.23/0.54        | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.54  thf('28', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d1_xboole_0, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.54  thf('29', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.54  thf('30', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.54  thf('31', plain, (((k6_domain_1 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.23/0.54      inference('clc', [status(thm)], ['27', '30'])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))
% 0.23/0.54        | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.54      inference('demod', [status(thm)], ['24', '31'])).
% 0.23/0.54  thf('33', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.23/0.54      inference('clc', [status(thm)], ['32', '33'])).
% 0.23/0.54  thf(t3_subset, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.54  thf('35', plain,
% 0.23/0.54      (![X5 : $i, X6 : $i]:
% 0.23/0.54         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.54  thf('36', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)),
% 0.23/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.23/0.54  thf('37', plain,
% 0.23/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.23/0.54            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.23/0.54        | (v2_struct_0 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['19', '36'])).
% 0.23/0.54  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('39', plain,
% 0.23/0.54      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.23/0.54          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))) = (k1_tarski @ sk_C_1))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('clc', [status(thm)], ['37', '38'])).
% 0.23/0.54  thf('40', plain,
% 0.23/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.54  thf('41', plain,
% 0.23/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.23/0.54         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.23/0.54         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('42', plain,
% 0.23/0.54      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.23/0.54          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.23/0.54          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.23/0.54  thf('43', plain,
% 0.23/0.54      ((((k1_tarski @ sk_C_1) != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['39', '42'])).
% 0.23/0.54  thf('44', plain,
% 0.23/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | ((k1_tarski @ sk_C_1)
% 0.23/0.54            != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['43'])).
% 0.23/0.54  thf('45', plain,
% 0.23/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.23/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.54  thf('46', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('clc', [status(thm)], ['44', '45'])).
% 0.23/0.54  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.23/0.54      inference('demod', [status(thm)], ['3', '46'])).
% 0.23/0.54  thf('48', plain, ($false), inference('sup-', [status(thm)], ['0', '47'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
