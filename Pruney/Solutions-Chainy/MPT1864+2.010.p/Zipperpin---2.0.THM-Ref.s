%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xj5n7WPnJp

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:18 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 173 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  631 (2302 expanded)
%              Number of equality atoms :   20 (  79 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(t32_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( v3_pre_topc @ D @ A )
                              & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                                = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_tex_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['3','6'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X36 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r2_hidden @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tex_2,axiom,(
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
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ( m1_subset_1 @ ( sk_D_1 @ X45 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( r1_tarski @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X36 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r2_hidden @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X47: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X47 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X47 @ sk_A )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v3_pre_topc @ ( sk_D_1 @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ( v3_pre_topc @ ( sk_D_1 @ X45 @ X43 @ X44 ) @ X44 )
      | ~ ( r1_tarski @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( v3_pre_topc @ ( sk_D_1 @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('40',plain,(
    v3_pre_topc @ ( sk_D_1 @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X44 ) @ X43 @ ( sk_D_1 @ X45 @ X43 @ X44 ) )
        = X45 )
      | ~ ( r1_tarski @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('50',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ( k1_tarski @ sk_C_1 )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','40','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xj5n7WPnJp
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 209 iterations in 0.100s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.37/0.55  thf(t32_tex_2, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ( v2_tex_2 @ B @ A ) =>
% 0.37/0.55             ( ![C:$i]:
% 0.37/0.55               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.37/0.55                      ( ![D:$i]:
% 0.37/0.55                        ( ( m1_subset_1 @
% 0.37/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.37/0.55                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.37/0.55                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( l1_pre_topc @ A ) =>
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55              ( ( v2_tex_2 @ B @ A ) =>
% 0.37/0.55                ( ![C:$i]:
% 0.37/0.55                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.37/0.55                         ( ![D:$i]:
% 0.37/0.55                           ( ( m1_subset_1 @
% 0.37/0.55                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55                             ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.37/0.55                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.37/0.55                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t32_tex_2])).
% 0.37/0.55  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t3_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X40 : $i, X41 : $i]:
% 0.37/0.55         ((r1_tarski @ X40 @ X41) | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf(t28_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i]:
% 0.37/0.55         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.55  thf(t12_setfam_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X38 : $i, X39 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i]:
% 0.37/0.55         (((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (X6))
% 0.37/0.55          | ~ (r1_tarski @ X6 @ X7))),
% 0.37/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '6'])).
% 0.37/0.55  thf(d4_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.55          | (r2_hidden @ X4 @ X2)
% 0.37/0.55          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X38 : $i, X39 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ X2)
% 0.37/0.55          | ~ (r2_hidden @ X4 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 0.37/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '11'])).
% 0.37/0.55  thf('13', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '12'])).
% 0.37/0.55  thf(t63_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r2_hidden @ A @ B ) =>
% 0.37/0.55       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X36 : $i, X37 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k1_tarski @ X36) @ (k1_zfmisc_1 @ X37))
% 0.37/0.55          | ~ (r2_hidden @ X36 @ X37))),
% 0.37/0.55      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.37/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d5_tex_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ( v2_tex_2 @ B @ A ) <=>
% 0.37/0.55             ( ![C:$i]:
% 0.37/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.37/0.55                      ( ![D:$i]:
% 0.37/0.55                        ( ( m1_subset_1 @
% 0.37/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.37/0.55                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.37/0.55                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.55          | ~ (v2_tex_2 @ X43 @ X44)
% 0.37/0.55          | (m1_subset_1 @ (sk_D_1 @ X45 @ X43 @ X44) @ 
% 0.37/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.55          | ~ (r1_tarski @ X45 @ X43)
% 0.37/0.55          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.55          | ~ (l1_pre_topc @ X44))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.55          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.37/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('20', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.55          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.37/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (((m1_subset_1 @ (sk_D_1 @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.37/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '21'])).
% 0.37/0.55  thf('23', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X36 : $i, X37 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k1_tarski @ X36) @ (k1_zfmisc_1 @ X37))
% 0.37/0.55          | ~ (r2_hidden @ X36 @ X37))),
% 0.37/0.55      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X40 : $i, X41 : $i]:
% 0.37/0.55         ((r1_tarski @ X40 @ X41) | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('27', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      ((m1_subset_1 @ (sk_D_1 @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.37/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['22', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X47 : $i]:
% 0.37/0.55         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X47)
% 0.37/0.55            != (k1_tarski @ sk_C_1))
% 0.37/0.55          | ~ (v3_pre_topc @ X47 @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((~ (v3_pre_topc @ (sk_D_1 @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.37/0.55        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55            (sk_D_1 @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.37/0.55            != (k1_tarski @ sk_C_1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.37/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.55          | ~ (v2_tex_2 @ X43 @ X44)
% 0.37/0.55          | (v3_pre_topc @ (sk_D_1 @ X45 @ X43 @ X44) @ X44)
% 0.37/0.55          | ~ (r1_tarski @ X45 @ X43)
% 0.37/0.55          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.55          | ~ (l1_pre_topc @ X44))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.55          | (v3_pre_topc @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.37/0.55          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.55  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('36', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.55          | (v3_pre_topc @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (((v3_pre_topc @ (sk_D_1 @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.37/0.55        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['31', '37'])).
% 0.37/0.55  thf('39', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      ((v3_pre_topc @ (sk_D_1 @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.37/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.37/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.55          | ~ (v2_tex_2 @ X43 @ X44)
% 0.37/0.55          | ((k9_subset_1 @ (u1_struct_0 @ X44) @ X43 @ 
% 0.37/0.55              (sk_D_1 @ X45 @ X43 @ X44)) = (X45))
% 0.37/0.55          | ~ (r1_tarski @ X45 @ X43)
% 0.37/0.55          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.55          | ~ (l1_pre_topc @ X44))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (X0))
% 0.37/0.55          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.55  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('46', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55          (sk_D_1 @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.37/0.55        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['41', '47'])).
% 0.37/0.55  thf('49', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55         (sk_D_1 @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.37/0.55  thf('51', plain, (((k1_tarski @ sk_C_1) != (k1_tarski @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['30', '40', '50'])).
% 0.37/0.55  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
