%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fDsgtoSsDi

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:17 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 210 expanded)
%              Number of leaves         :   23 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  638 (3607 expanded)
%              Number of equality atoms :   30 ( 130 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('2',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( m1_subset_1 @ ( k1_tarski @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ ( sk_D @ X17 @ X15 @ X16 ) )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_D @ X17 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X19: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X19 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X19 @ sk_A )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( v3_pre_topc @ ( sk_D @ X17 @ X15 @ X16 ) @ X16 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('43',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['33','43'])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['21','44'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['21','44'])).

thf('48',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['7','45','46','47'])).

thf('49',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['2','48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fDsgtoSsDi
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 234 iterations in 0.116s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.55  thf(t32_tex_2, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v2_tex_2 @ B @ A ) =>
% 0.36/0.55             ( ![C:$i]:
% 0.36/0.55               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.36/0.55                      ( ![D:$i]:
% 0.36/0.55                        ( ( m1_subset_1 @
% 0.36/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.36/0.55                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.36/0.55                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( l1_pre_topc @ A ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55              ( ( v2_tex_2 @ B @ A ) =>
% 0.36/0.55                ( ![C:$i]:
% 0.36/0.55                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.36/0.55                         ( ![D:$i]:
% 0.36/0.55                           ( ( m1_subset_1 @
% 0.36/0.55                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55                             ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.36/0.55                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.36/0.55                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t32_tex_2])).
% 0.36/0.55  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t7_ordinal1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.36/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.55  thf('2', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t3_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('5', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf(d10_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X0 : $i, X2 : $i]:
% 0.36/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.55  thf('8', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t55_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ A ) =>
% 0.36/0.55       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.36/0.55         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         (((X8) = (k1_xboole_0))
% 0.36/0.55          | ~ (m1_subset_1 @ X9 @ X8)
% 0.36/0.55          | (m1_subset_1 @ (k1_tarski @ X9) @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d5_tex_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v2_tex_2 @ B @ A ) <=>
% 0.36/0.55             ( ![C:$i]:
% 0.36/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.36/0.55                      ( ![D:$i]:
% 0.36/0.55                        ( ( m1_subset_1 @
% 0.36/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.36/0.55                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.36/0.55                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.55          | ~ (v2_tex_2 @ X15 @ X16)
% 0.36/0.55          | ((k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ 
% 0.36/0.55              (sk_D @ X17 @ X15 @ X16)) = (X17))
% 0.36/0.55          | ~ (r1_tarski @ X17 @ X15)
% 0.36/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.55          | ~ (l1_pre_topc @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.36/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.55              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.36/0.55          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('15', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.36/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.55              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.36/0.55      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.55            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.36/0.55        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '16'])).
% 0.36/0.55  thf('18', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(l1_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X5 : $i, X7 : $i]:
% 0.36/0.55         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 0.36/0.55      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.55  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.55            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1)))),
% 0.36/0.55      inference('demod', [status(thm)], ['17', '20'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.55          | ~ (v2_tex_2 @ X15 @ X16)
% 0.36/0.55          | (m1_subset_1 @ (sk_D @ X17 @ X15 @ X16) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.55          | ~ (r1_tarski @ X17 @ X15)
% 0.36/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.55          | ~ (l1_pre_topc @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.36/0.55          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.36/0.55          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '28'])).
% 0.36/0.55  thf('30', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X19 : $i]:
% 0.36/0.55         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X19)
% 0.36/0.55            != (k1_tarski @ sk_C_1))
% 0.36/0.55          | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | ~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.36/0.55        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.55            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.36/0.55            != (k1_tarski @ sk_C_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.55          | ~ (v2_tex_2 @ X15 @ X16)
% 0.36/0.55          | (v3_pre_topc @ (sk_D @ X17 @ X15 @ X16) @ X16)
% 0.36/0.55          | ~ (r1_tarski @ X17 @ X15)
% 0.36/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.55          | ~ (l1_pre_topc @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.36/0.55          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.36/0.55          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('39', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.36/0.55          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.36/0.55        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['34', '40'])).
% 0.36/0.55  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.55          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_1))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('clc', [status(thm)], ['33', '43'])).
% 0.36/0.55  thf('45', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('clc', [status(thm)], ['21', '44'])).
% 0.36/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.55  thf('46', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf('47', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('clc', [status(thm)], ['21', '44'])).
% 0.36/0.55  thf('48', plain, (((k1_xboole_0) = (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['7', '45', '46', '47'])).
% 0.36/0.55  thf('49', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf('50', plain, ($false),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '48', '49'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
