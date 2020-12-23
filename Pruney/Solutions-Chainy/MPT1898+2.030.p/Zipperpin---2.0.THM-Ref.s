%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c0RifmQj3o

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  92 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  453 ( 870 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ X7 )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v3_tdlat_3 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t59_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( v3_tex_2 @ ( sk_C_1 @ X11 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

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

thf('19',plain,(
    ! [X13: $i] :
      ( ~ ( v3_tex_2 @ X13 @ sk_A )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c0RifmQj3o
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 39 iterations in 0.043s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.50  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.50  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf(t4_subset_1, axiom,
% 0.20/0.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.50  thf(t59_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.50         ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.50             ( ![C:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                 ( ![D:$i]:
% 0.20/0.50                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                     ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) ) =>
% 0.20/0.50                       ( ( ( C ) = ( D ) ) | 
% 0.20/0.50                         ( r1_xboole_0 @
% 0.20/0.50                           ( k2_pre_topc @
% 0.20/0.50                             A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.20/0.50                           ( k2_pre_topc @
% 0.20/0.50                             A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X7 @ X8) @ X7)
% 0.20/0.50          | (v2_tex_2 @ X7 @ X8)
% 0.20/0.50          | ~ (l1_pre_topc @ X8)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X8)
% 0.20/0.50          | ~ (v2_pre_topc @ X8)
% 0.20/0.50          | (v2_struct_0 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t59_tex_2])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.50          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.50  thf(t5_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.50          | ~ (v1_xboole_0 @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.50  thf(t65_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.50         ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.50                ( ![C:$i]:
% 0.20/0.50                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.50          | ~ (v2_tex_2 @ X11 @ X12)
% 0.20/0.50          | (v3_tex_2 @ (sk_C_1 @ X11 @ X12) @ X12)
% 0.20/0.50          | ~ (l1_pre_topc @ X12)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X12)
% 0.20/0.50          | ~ (v2_pre_topc @ X12)
% 0.20/0.50          | (v2_struct_0 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.50          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X1)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.50          | ~ (v2_tex_2 @ X11 @ X12)
% 0.20/0.50          | (m1_subset_1 @ (sk_C_1 @ X11 @ X12) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.50          | ~ (l1_pre_topc @ X12)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X12)
% 0.20/0.50          | ~ (v2_pre_topc @ X12)
% 0.20/0.50          | (v2_struct_0 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X1)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf(t66_tex_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.50         ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ?[B:$i]:
% 0.20/0.50         ( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.50           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ?[B:$i]:
% 0.20/0.50            ( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.50              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X13 : $i]:
% 0.20/0.50         (~ (v3_tex_2 @ X13 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.50  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)
% 0.20/0.50          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X1)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '26'])).
% 0.20/0.50  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X1) | (v2_struct_0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.20/0.50  thf('32', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('condensation', [status(thm)], ['31'])).
% 0.20/0.50  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.20/0.50      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, ($false), inference('sup-', [status(thm)], ['0', '34'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
