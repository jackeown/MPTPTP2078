%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E6FMlgLqqv

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:31 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 161 expanded)
%              Number of leaves         :   25 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  475 (1031 expanded)
%              Number of equality atoms :   25 (  53 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('2',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v2_tex_2 @ sk_A @ sk_A_1 ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( sk_B @ X21 ) @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('10',plain,(
    ! [X21: $i] :
      ( v1_xboole_0 @ ( sk_B @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ X29 @ X30 )
      | ~ ( v1_xboole_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ( v4_pre_topc @ X0 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('22',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(d6_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X31: $i,X32: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v4_pre_topc @ X34 @ X32 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ X34 )
       != ( sk_C_2 @ X31 @ X32 ) )
      | ( v2_tex_2 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ sk_A @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_A @ X1 )
       != ( sk_C_2 @ sk_A @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ sk_A @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_A @ sk_A )
       != ( sk_C_2 @ sk_A @ X0 ) )
      | ( v2_tex_2 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X19 @ X18 @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ sk_A @ X0 )
      | ( sk_A
       != ( sk_C_2 @ sk_A @ X0 ) )
      | ( v2_tex_2 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['25','31'])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ( v2_tex_2 @ sk_A @ sk_A_1 )
    | ( sk_A
     != ( sk_C_2 @ sk_A @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('37',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r1_tarski @ ( sk_C_2 @ X31 @ X32 ) @ X31 )
      | ( v2_tex_2 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_2 @ sk_A @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    ~ ( v2_tex_2 @ sk_A @ sk_A_1 ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( sk_C_2 @ sk_A @ sk_A_1 )
      = sk_A )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('51',plain,
    ( ( sk_C_2 @ sk_A @ sk_A_1 )
    = sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v2_tex_2 @ sk_A @ sk_A_1 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['33','34','35','51'])).

thf('53',plain,(
    v2_tex_2 @ sk_A @ sk_A_1 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['6','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E6FMlgLqqv
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:23:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.05/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.27  % Solved by: fo/fo7.sh
% 1.05/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.27  % done 1349 iterations in 0.816s
% 1.05/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.27  % SZS output start Refutation
% 1.05/1.27  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.05/1.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.27  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.05/1.27  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.05/1.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.05/1.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.05/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.27  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.05/1.27  thf(sk_A_1_type, type, sk_A_1: $i).
% 1.05/1.27  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.05/1.27  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.05/1.27  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.05/1.27  thf(sk_B_type, type, sk_B: $i > $i).
% 1.05/1.27  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.05/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.27  thf(t35_tex_2, conjecture,
% 1.05/1.27    (![A:$i]:
% 1.05/1.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.05/1.27       ( ![B:$i]:
% 1.05/1.27         ( ( ( v1_xboole_0 @ B ) & 
% 1.05/1.27             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.27           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.05/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.27    (~( ![A:$i]:
% 1.05/1.27        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.05/1.27            ( l1_pre_topc @ A ) ) =>
% 1.05/1.27          ( ![B:$i]:
% 1.05/1.27            ( ( ( v1_xboole_0 @ B ) & 
% 1.05/1.27                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.27              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 1.05/1.27    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 1.05/1.27  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 1.05/1.27  thf('2', plain, ((v1_xboole_0 @ sk_A)),
% 1.05/1.27      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 1.05/1.27  thf(t8_boole, axiom,
% 1.05/1.27    (![A:$i,B:$i]:
% 1.05/1.27     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.05/1.27  thf('3', plain,
% 1.05/1.27      (![X7 : $i, X8 : $i]:
% 1.05/1.27         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 1.05/1.27      inference('cnf', [status(esa)], [t8_boole])).
% 1.05/1.27  thf('4', plain, (![X0 : $i]: (((sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.27  thf('5', plain, (((sk_A) = (sk_B_1))),
% 1.05/1.27      inference('sup-', [status(thm)], ['1', '4'])).
% 1.05/1.27  thf('6', plain, (~ (v2_tex_2 @ sk_A @ sk_A_1)),
% 1.05/1.27      inference('demod', [status(thm)], ['0', '5'])).
% 1.05/1.27  thf('7', plain, ((l1_pre_topc @ sk_A_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('8', plain, (![X0 : $i]: (((sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.27  thf(rc2_subset_1, axiom,
% 1.05/1.27    (![A:$i]:
% 1.05/1.27     ( ?[B:$i]:
% 1.05/1.27       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.05/1.27  thf('9', plain,
% 1.05/1.27      (![X21 : $i]: (m1_subset_1 @ (sk_B @ X21) @ (k1_zfmisc_1 @ X21))),
% 1.05/1.27      inference('cnf', [status(esa)], [rc2_subset_1])).
% 1.05/1.27  thf('10', plain, (![X21 : $i]: (v1_xboole_0 @ (sk_B @ X21))),
% 1.05/1.27      inference('cnf', [status(esa)], [rc2_subset_1])).
% 1.05/1.27  thf('11', plain, (![X0 : $i]: (((sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.27  thf('12', plain, (![X0 : $i]: ((sk_A) = (sk_B @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['10', '11'])).
% 1.05/1.27  thf('13', plain, (![X21 : $i]: (m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ X21))),
% 1.05/1.27      inference('demod', [status(thm)], ['9', '12'])).
% 1.05/1.27  thf('14', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i]:
% 1.05/1.27         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.27      inference('sup+', [status(thm)], ['8', '13'])).
% 1.05/1.27  thf(cc2_pre_topc, axiom,
% 1.05/1.27    (![A:$i]:
% 1.05/1.27     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.05/1.27       ( ![B:$i]:
% 1.05/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.27           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 1.05/1.27  thf('15', plain,
% 1.05/1.27      (![X29 : $i, X30 : $i]:
% 1.05/1.27         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.05/1.27          | (v4_pre_topc @ X29 @ X30)
% 1.05/1.27          | ~ (v1_xboole_0 @ X29)
% 1.05/1.27          | ~ (l1_pre_topc @ X30)
% 1.05/1.27          | ~ (v2_pre_topc @ X30))),
% 1.05/1.27      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 1.05/1.27  thf('16', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i]:
% 1.05/1.27         (~ (v1_xboole_0 @ X1)
% 1.05/1.27          | ~ (v2_pre_topc @ X0)
% 1.05/1.27          | ~ (l1_pre_topc @ X0)
% 1.05/1.27          | ~ (v1_xboole_0 @ X1)
% 1.05/1.27          | (v4_pre_topc @ X1 @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['14', '15'])).
% 1.05/1.27  thf('17', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i]:
% 1.05/1.27         ((v4_pre_topc @ X1 @ X0)
% 1.05/1.27          | ~ (l1_pre_topc @ X0)
% 1.05/1.27          | ~ (v2_pre_topc @ X0)
% 1.05/1.27          | ~ (v1_xboole_0 @ X1))),
% 1.05/1.27      inference('simplify', [status(thm)], ['16'])).
% 1.05/1.27  thf('18', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (~ (v1_xboole_0 @ X0)
% 1.05/1.27          | ~ (v2_pre_topc @ sk_A_1)
% 1.05/1.27          | (v4_pre_topc @ X0 @ sk_A_1))),
% 1.05/1.27      inference('sup-', [status(thm)], ['7', '17'])).
% 1.05/1.27  thf('19', plain, ((v2_pre_topc @ sk_A_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('20', plain,
% 1.05/1.27      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A_1))),
% 1.05/1.27      inference('demod', [status(thm)], ['18', '19'])).
% 1.05/1.27  thf('21', plain, (![X21 : $i]: (m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ X21))),
% 1.05/1.27      inference('demod', [status(thm)], ['9', '12'])).
% 1.05/1.27  thf('22', plain, (![X21 : $i]: (m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ X21))),
% 1.05/1.27      inference('demod', [status(thm)], ['9', '12'])).
% 1.05/1.27  thf(d6_tex_2, axiom,
% 1.05/1.27    (![A:$i]:
% 1.05/1.27     ( ( l1_pre_topc @ A ) =>
% 1.05/1.27       ( ![B:$i]:
% 1.05/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.27           ( ( v2_tex_2 @ B @ A ) <=>
% 1.05/1.27             ( ![C:$i]:
% 1.05/1.27               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.27                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.05/1.27                      ( ![D:$i]:
% 1.05/1.27                        ( ( m1_subset_1 @
% 1.05/1.27                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.27                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.05/1.27                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.05/1.27                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.05/1.27  thf('23', plain,
% 1.05/1.27      (![X31 : $i, X32 : $i, X34 : $i]:
% 1.05/1.27         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.05/1.27          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.05/1.27          | ~ (v4_pre_topc @ X34 @ X32)
% 1.05/1.27          | ((k9_subset_1 @ (u1_struct_0 @ X32) @ X31 @ X34)
% 1.05/1.27              != (sk_C_2 @ X31 @ X32))
% 1.05/1.27          | (v2_tex_2 @ X31 @ X32)
% 1.05/1.27          | ~ (l1_pre_topc @ X32))),
% 1.05/1.27      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.05/1.27  thf('24', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i]:
% 1.05/1.27         (~ (l1_pre_topc @ X0)
% 1.05/1.27          | (v2_tex_2 @ sk_A @ X0)
% 1.05/1.27          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ sk_A @ X1)
% 1.05/1.27              != (sk_C_2 @ sk_A @ X0))
% 1.05/1.27          | ~ (v4_pre_topc @ X1 @ X0)
% 1.05/1.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.05/1.27      inference('sup-', [status(thm)], ['22', '23'])).
% 1.05/1.27  thf('25', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (~ (v4_pre_topc @ sk_A @ X0)
% 1.05/1.27          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ sk_A @ sk_A)
% 1.05/1.27              != (sk_C_2 @ sk_A @ X0))
% 1.05/1.27          | (v2_tex_2 @ sk_A @ X0)
% 1.05/1.27          | ~ (l1_pre_topc @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['21', '24'])).
% 1.05/1.27  thf(d10_xboole_0, axiom,
% 1.05/1.27    (![A:$i,B:$i]:
% 1.05/1.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.05/1.27  thf('26', plain,
% 1.05/1.27      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.05/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.27  thf('27', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.05/1.27      inference('simplify', [status(thm)], ['26'])).
% 1.05/1.27  thf(t3_subset, axiom,
% 1.05/1.27    (![A:$i,B:$i]:
% 1.05/1.27     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.05/1.27  thf('28', plain,
% 1.05/1.27      (![X22 : $i, X24 : $i]:
% 1.05/1.27         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 1.05/1.27      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.27  thf('29', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['27', '28'])).
% 1.05/1.27  thf(idempotence_k9_subset_1, axiom,
% 1.05/1.27    (![A:$i,B:$i,C:$i]:
% 1.05/1.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.27       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 1.05/1.27  thf('30', plain,
% 1.05/1.27      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.27         (((k9_subset_1 @ X19 @ X18 @ X18) = (X18))
% 1.05/1.27          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 1.05/1.27      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 1.05/1.27  thf('31', plain,
% 1.05/1.27      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 1.05/1.27      inference('sup-', [status(thm)], ['29', '30'])).
% 1.05/1.27  thf('32', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (~ (v4_pre_topc @ sk_A @ X0)
% 1.05/1.27          | ((sk_A) != (sk_C_2 @ sk_A @ X0))
% 1.05/1.27          | (v2_tex_2 @ sk_A @ X0)
% 1.05/1.27          | ~ (l1_pre_topc @ X0))),
% 1.05/1.27      inference('demod', [status(thm)], ['25', '31'])).
% 1.05/1.27  thf('33', plain,
% 1.05/1.27      ((~ (v1_xboole_0 @ sk_A)
% 1.05/1.27        | ~ (l1_pre_topc @ sk_A_1)
% 1.05/1.27        | (v2_tex_2 @ sk_A @ sk_A_1)
% 1.05/1.27        | ((sk_A) != (sk_C_2 @ sk_A @ sk_A_1)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['20', '32'])).
% 1.05/1.27  thf('34', plain, ((v1_xboole_0 @ sk_A)),
% 1.05/1.27      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 1.05/1.27  thf('35', plain, ((l1_pre_topc @ sk_A_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('36', plain, (![X21 : $i]: (m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ X21))),
% 1.05/1.27      inference('demod', [status(thm)], ['9', '12'])).
% 1.05/1.27  thf('37', plain,
% 1.05/1.27      (![X31 : $i, X32 : $i]:
% 1.05/1.27         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.05/1.27          | (r1_tarski @ (sk_C_2 @ X31 @ X32) @ X31)
% 1.05/1.27          | (v2_tex_2 @ X31 @ X32)
% 1.05/1.27          | ~ (l1_pre_topc @ X32))),
% 1.05/1.27      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.05/1.27  thf('38', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (~ (l1_pre_topc @ X0)
% 1.05/1.27          | (v2_tex_2 @ sk_A @ X0)
% 1.05/1.27          | (r1_tarski @ (sk_C_2 @ sk_A @ X0) @ sk_A))),
% 1.05/1.27      inference('sup-', [status(thm)], ['36', '37'])).
% 1.05/1.27  thf('39', plain, (![X21 : $i]: (m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ X21))),
% 1.05/1.27      inference('demod', [status(thm)], ['9', '12'])).
% 1.05/1.27  thf('40', plain,
% 1.05/1.27      (![X22 : $i, X23 : $i]:
% 1.05/1.27         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 1.05/1.27      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.27  thf('41', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 1.05/1.27      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.27  thf('42', plain,
% 1.05/1.27      (![X2 : $i, X4 : $i]:
% 1.05/1.27         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.05/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.27  thf('43', plain, (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_A) | ((X0) = (sk_A)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['41', '42'])).
% 1.05/1.27  thf('44', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         ((v2_tex_2 @ sk_A @ X0)
% 1.05/1.27          | ~ (l1_pre_topc @ X0)
% 1.05/1.27          | ((sk_C_2 @ sk_A @ X0) = (sk_A)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['38', '43'])).
% 1.05/1.27  thf('45', plain, (![X0 : $i]: (((sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.27  thf('46', plain, (~ (v2_tex_2 @ sk_A @ sk_A_1)),
% 1.05/1.27      inference('demod', [status(thm)], ['0', '5'])).
% 1.05/1.27  thf('47', plain,
% 1.05/1.27      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A_1) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.27      inference('sup-', [status(thm)], ['45', '46'])).
% 1.05/1.27  thf('48', plain,
% 1.05/1.27      ((((sk_C_2 @ sk_A @ sk_A_1) = (sk_A))
% 1.05/1.27        | ~ (l1_pre_topc @ sk_A_1)
% 1.05/1.27        | ~ (v1_xboole_0 @ sk_A))),
% 1.05/1.27      inference('sup-', [status(thm)], ['44', '47'])).
% 1.05/1.27  thf('49', plain, ((l1_pre_topc @ sk_A_1)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('50', plain, ((v1_xboole_0 @ sk_A)),
% 1.05/1.27      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 1.05/1.27  thf('51', plain, (((sk_C_2 @ sk_A @ sk_A_1) = (sk_A))),
% 1.05/1.27      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.05/1.27  thf('52', plain, (((v2_tex_2 @ sk_A @ sk_A_1) | ((sk_A) != (sk_A)))),
% 1.05/1.27      inference('demod', [status(thm)], ['33', '34', '35', '51'])).
% 1.05/1.27  thf('53', plain, ((v2_tex_2 @ sk_A @ sk_A_1)),
% 1.05/1.27      inference('simplify', [status(thm)], ['52'])).
% 1.05/1.27  thf('54', plain, ($false), inference('demod', [status(thm)], ['6', '53'])).
% 1.05/1.27  
% 1.05/1.27  % SZS output end Refutation
% 1.05/1.27  
% 1.05/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
