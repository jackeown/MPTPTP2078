%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jzg5JZHt53

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 221 expanded)
%              Number of leaves         :   23 (  74 expanded)
%              Depth                    :   18
%              Number of atoms          :  559 (3254 expanded)
%              Number of equality atoms :   24 ( 110 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t53_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v3_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ~ ( ( v4_tex_2 @ C @ A )
                      & ( B
                        = ( u1_struct_0 @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( v3_tex_2 @ B @ A )
                & ! [C: $i] :
                    ( ( ~ ( v2_struct_0 @ C )
                      & ( v1_pre_topc @ C )
                      & ( m1_pre_topc @ C @ A ) )
                   => ~ ( ( v4_tex_2 @ C @ A )
                        & ( B
                          = ( u1_struct_0 @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ~ ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('11',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','19'])).

thf('21',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( sk_C @ X8 @ X9 )
        = ( u1_struct_0 @ X8 ) )
      | ( v4_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = sk_B )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v4_tex_2 @ X11 @ sk_A )
      | ~ ( m1_pre_topc @ X11 @ sk_A )
      | ~ ( v1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( sk_B
     != ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('33',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('37',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf('38',plain,
    ( ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['30','35','36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','19'])).

thf('41',plain,
    ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    = sk_B ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v3_tex_2 @ ( sk_C @ X8 @ X9 ) @ X9 )
      | ( v4_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('43',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v4_tex_2 @ X11 @ sk_A )
      | ~ ( m1_pre_topc @ X11 @ sk_A )
      | ~ ( v1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( sk_B
     != ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('53',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('54',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf('55',plain,
    ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['20','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jzg5JZHt53
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 41 iterations in 0.023s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.20/0.47  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(t53_tex_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47           ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.47                ( ![C:$i]:
% 0.20/0.47                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.47                      ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.47                    ( ~( ( v4_tex_2 @ C @ A ) & ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47              ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.47                   ( ![C:$i]:
% 0.20/0.47                     ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.47                         ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.47                       ( ~( ( v4_tex_2 @ C @ A ) & 
% 0.20/0.47                            ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t53_tex_2])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t29_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.47          | ((u1_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.20/0.47          | ~ (l1_pre_topc @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(fc1_struct_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X5 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.20/0.47          | ~ (l1_struct_0 @ X5)
% 0.20/0.47          | ~ (v2_struct_0 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B)
% 0.20/0.47        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.47        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      ((~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k1_pre_topc, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.20/0.47         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | (m1_pre_topc @ (k1_pre_topc @ X0 @ X1) @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf(dt_m1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf(dt_l1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.47  thf('18', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.47  thf('19', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, (~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '19'])).
% 0.20/0.47  thf('21', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf(d8_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.47           ( ( v4_tex_2 @ B @ A ) <=>
% 0.20/0.47             ( ![C:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.47          | ((sk_C @ X8 @ X9) = (u1_struct_0 @ X8))
% 0.20/0.47          | (v4_tex_2 @ X8 @ X9)
% 0.20/0.47          | ~ (l1_pre_topc @ X9)
% 0.20/0.47          | (v2_struct_0 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.47        | ((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.47            = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.47        | ((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A) = (sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.47  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A) = (sk_B))
% 0.20/0.47        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X11 : $i]:
% 0.20/0.47         (((sk_B) != (u1_struct_0 @ X11))
% 0.20/0.47          | ~ (v4_tex_2 @ X11 @ sk_A)
% 0.20/0.47          | ~ (m1_pre_topc @ X11 @ sk_A)
% 0.20/0.47          | ~ (v1_pre_topc @ X11)
% 0.20/0.47          | (v2_struct_0 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A) = (sk_B))
% 0.20/0.47        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.47        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.47        | ((sk_B) != (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | (v1_pre_topc @ (k1_pre_topc @ X0 @ X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('37', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A) = (sk_B))
% 0.20/0.47        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.47        | ((sk_B) != (sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['30', '35', '36', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.47        | ((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A) = (sk_B)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.47  thf('40', plain, (~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '19'])).
% 0.20/0.47  thf('41', plain, (((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A) = (sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.47          | ~ (v3_tex_2 @ (sk_C @ X8 @ X9) @ X9)
% 0.20/0.47          | (v4_tex_2 @ X8 @ X9)
% 0.20/0.47          | ~ (l1_pre_topc @ X9)
% 0.20/0.47          | (v2_struct_0 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      ((~ (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.47        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.47  thf('44', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('46', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A) | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.20/0.47  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('49', plain, ((v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      (![X11 : $i]:
% 0.20/0.47         (((sk_B) != (u1_struct_0 @ X11))
% 0.20/0.47          | ~ (v4_tex_2 @ X11 @ sk_A)
% 0.20/0.47          | ~ (m1_pre_topc @ X11 @ sk_A)
% 0.20/0.47          | ~ (v1_pre_topc @ X11)
% 0.20/0.47          | (v2_struct_0 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      (((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.47        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.47        | ((sk_B) != (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.47  thf('52', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('53', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('54', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('55', plain,
% 0.20/0.47      (((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) | ((sk_B) != (sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.20/0.47  thf('56', plain, ((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.47      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.47  thf('57', plain, ($false), inference('demod', [status(thm)], ['20', '56'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
