%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tIca57gkzO

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 103 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  479 ( 987 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(t66_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_tex_2 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ? [B: $i] :
            ( ( v3_tex_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tex_2])).

thf('0',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc1_connsp_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t59_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r2_hidden @ D @ B ) )
                     => ( ( C = D )
                        | ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ D ) ) ) ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X11 ) @ X10 )
      | ( v2_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t59_tex_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( v3_tdlat_3 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( v3_tex_2 @ ( sk_C_1 @ X14 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v3_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( v3_tdlat_3 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( m1_subset_1 @ ( sk_C_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v3_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X16: $i] :
      ( ~ ( v3_tex_2 @ X16 @ sk_A )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( l1_pre_topc @ X0 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tIca57gkzO
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 58 iterations in 0.049s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.19/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.19/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.50  thf(t66_tex_2, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.50         ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ?[B:$i]:
% 0.19/0.50         ( ( v3_tex_2 @ B @ A ) & 
% 0.19/0.50           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.50            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50          ( ?[B:$i]:
% 0.19/0.50            ( ( v3_tex_2 @ B @ A ) & 
% 0.19/0.50              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.19/0.50  thf('0', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(rc1_connsp_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ?[B:$i]:
% 0.19/0.50         ( ( v1_xboole_0 @ B ) & 
% 0.19/0.50           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X9 : $i]: ((v1_xboole_0 @ (sk_B @ X9)) | ~ (l1_pre_topc @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.19/0.50  thf(t4_subset_1, axiom,
% 0.19/0.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.50  thf(t59_tex_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.50         ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50           ( ( v2_tex_2 @ B @ A ) <=>
% 0.19/0.50             ( ![C:$i]:
% 0.19/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50                 ( ![D:$i]:
% 0.19/0.50                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50                     ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) ) =>
% 0.19/0.50                       ( ( ( C ) = ( D ) ) | 
% 0.19/0.50                         ( r1_xboole_0 @
% 0.19/0.50                           ( k2_pre_topc @
% 0.19/0.50                             A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.19/0.50                           ( k2_pre_topc @
% 0.19/0.50                             A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.19/0.50          | (r2_hidden @ (sk_D @ X10 @ X11) @ X10)
% 0.19/0.50          | (v2_tex_2 @ X10 @ X11)
% 0.19/0.50          | ~ (l1_pre_topc @ X11)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X11)
% 0.19/0.50          | ~ (v2_pre_topc @ X11)
% 0.19/0.50          | (v2_struct_0 @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [t59_tex_2])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.19/0.50          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.50  thf(t5_subset, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.19/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X6 @ X7)
% 0.19/0.50          | ~ (v1_xboole_0 @ X8)
% 0.19/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | (v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v1_xboole_0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (l1_pre_topc @ X0)
% 0.19/0.50          | (v2_struct_0 @ X1)
% 0.19/0.50          | ~ (v2_pre_topc @ X1)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X1)
% 0.19/0.50          | ~ (l1_pre_topc @ X1)
% 0.19/0.50          | (v2_tex_2 @ k1_xboole_0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | (v2_struct_0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.50  thf(t65_tex_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.50         ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.19/0.50                ( ![C:$i]:
% 0.19/0.50                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.19/0.50          | ~ (v2_tex_2 @ X14 @ X15)
% 0.19/0.50          | (v3_tex_2 @ (sk_C_1 @ X14 @ X15) @ X15)
% 0.19/0.50          | ~ (l1_pre_topc @ X15)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X15)
% 0.19/0.50          | ~ (v2_pre_topc @ X15)
% 0.19/0.50          | (v2_struct_0 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.19/0.50          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | (v2_struct_0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | (v2_struct_0 @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (l1_pre_topc @ X0)
% 0.19/0.50          | (v2_struct_0 @ X1)
% 0.19/0.50          | ~ (v2_pre_topc @ X1)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X1)
% 0.19/0.50          | ~ (l1_pre_topc @ X1)
% 0.19/0.50          | (v2_tex_2 @ k1_xboole_0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '9'])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.19/0.50          | ~ (v2_tex_2 @ X14 @ X15)
% 0.19/0.50          | (m1_subset_1 @ (sk_C_1 @ X14 @ X15) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.19/0.50          | ~ (l1_pre_topc @ X15)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X15)
% 0.19/0.50          | ~ (v2_pre_topc @ X15)
% 0.19/0.50          | (v2_struct_0 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | (v2_struct_0 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X1)
% 0.19/0.50          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | (v2_struct_0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['17', '20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.19/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (l1_pre_topc @ X1)
% 0.19/0.50          | (v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X16 : $i]:
% 0.19/0.50         (~ (v3_tex_2 @ X16 @ sk_A)
% 0.19/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | ~ (v3_tdlat_3 @ sk_A)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.50          | (v2_struct_0 @ sk_A)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('26', plain, ((v3_tdlat_3 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_A)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.19/0.50  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)
% 0.19/0.50          | ~ (l1_pre_topc @ X0))),
% 0.19/0.50      inference('clc', [status(thm)], ['28', '29'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_A)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.50          | ~ (v3_tdlat_3 @ sk_A)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | ~ (l1_pre_topc @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '30'])).
% 0.19/0.50  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('33', plain, ((v3_tdlat_3 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('35', plain, (![X0 : $i]: ((v2_struct_0 @ sk_A) | ~ (l1_pre_topc @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.19/0.50  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('37', plain, (![X0 : $i]: ~ (l1_pre_topc @ X0)),
% 0.19/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.19/0.50  thf('38', plain, ($false), inference('sup-', [status(thm)], ['0', '37'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
