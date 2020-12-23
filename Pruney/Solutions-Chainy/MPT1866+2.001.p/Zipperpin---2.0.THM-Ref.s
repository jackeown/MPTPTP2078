%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.82xo0OQ3PA

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 187 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  561 (3023 expanded)
%              Number of equality atoms :   15 ( 102 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(t34_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( v2_tex_2 @ B @ A )
                & ! [C: $i] :
                    ( ( ~ ( v2_struct_0 @ C )
                      & ( v1_pre_topc @ C )
                      & ( v1_tdlat_3 @ C )
                      & ( m1_pre_topc @ C @ A ) )
                   => ( B
                     != ( u1_struct_0 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X5 ) )
      | ~ ( m1_pre_topc @ X5 @ sk_A )
      | ~ ( v1_tdlat_3 @ X5 )
      | ~ ( v1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
     != ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v1_pre_topc @ ( sk_C @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0
        = ( u1_struct_0 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['19','28','37'])).

thf('39',plain,
    ( ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( X4
       != ( u1_struct_0 @ X2 ) )
      | ~ ( v2_tex_2 @ X4 @ X3 )
      | ( v1_tdlat_3 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v1_tdlat_3 @ X2 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X2 ) @ X3 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ sk_B @ X0 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('55',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['8','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.82xo0OQ3PA
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:25:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 22 iterations in 0.017s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.47  thf(t34_tex_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.47                ( ![C:$i]:
% 0.20/0.47                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.47                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.47                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47              ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.47                   ( ![C:$i]:
% 0.20/0.47                     ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.47                         ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.47                       ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t34_tex_2])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t10_tsep_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47           ( ?[C:$i]:
% 0.20/0.47             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.20/0.47               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.47          | ~ (v2_struct_0 @ (sk_C @ X0 @ X1))
% 0.20/0.47          | ~ (l1_pre_topc @ X1)
% 0.20/0.47          | (v2_struct_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | (v1_xboole_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | (v1_xboole_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.47          | (m1_pre_topc @ (sk_C @ X0 @ X1) @ X1)
% 0.20/0.47          | ~ (l1_pre_topc @ X1)
% 0.20/0.47          | (v2_struct_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.47        | (v1_xboole_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.47        | (v1_xboole_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X5 : $i]:
% 0.20/0.47         (((sk_B) != (u1_struct_0 @ X5))
% 0.20/0.47          | ~ (m1_pre_topc @ X5 @ sk_A)
% 0.20/0.47          | ~ (v1_tdlat_3 @ X5)
% 0.20/0.47          | ~ (v1_pre_topc @ X5)
% 0.20/0.47          | (v2_struct_0 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | ~ (v1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | ((sk_B) != (u1_struct_0 @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.47          | (v1_pre_topc @ (sk_C @ X0 @ X1))
% 0.20/0.47          | ~ (l1_pre_topc @ X1)
% 0.20/0.47          | (v2_struct_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | (v1_xboole_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (v1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | (v1_xboole_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B) | (v1_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('28', plain, ((v1_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.47          | ((X0) = (u1_struct_0 @ (sk_C @ X0 @ X1)))
% 0.20/0.47          | ~ (l1_pre_topc @ X1)
% 0.20/0.47          | (v2_struct_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.47        | (v1_xboole_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.47        | (v1_xboole_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B) | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.47      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | ((sk_B) != (sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['19', '28', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      ((~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf(t26_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.47                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X2)
% 0.20/0.47          | ~ (m1_pre_topc @ X2 @ X3)
% 0.20/0.47          | ((X4) != (u1_struct_0 @ X2))
% 0.20/0.47          | ~ (v2_tex_2 @ X4 @ X3)
% 0.20/0.47          | (v1_tdlat_3 @ X2)
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.47          | ~ (l1_pre_topc @ X3)
% 0.20/0.47          | (v2_struct_0 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X3)
% 0.20/0.47          | ~ (l1_pre_topc @ X3)
% 0.20/0.47          | ~ (m1_subset_1 @ (u1_struct_0 @ X2) @ 
% 0.20/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.47          | (v1_tdlat_3 @ X2)
% 0.20/0.47          | ~ (v2_tex_2 @ (u1_struct_0 @ X2) @ X3)
% 0.20/0.47          | ~ (m1_pre_topc @ X2 @ X3)
% 0.20/0.47          | (v2_struct_0 @ X2))),
% 0.20/0.47      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.47          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ X0)
% 0.20/0.47          | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['41', '43'])).
% 0.20/0.47  thf('45', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.47          | ~ (v2_tex_2 @ sk_B @ X0)
% 0.20/0.47          | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.47        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['40', '46'])).
% 0.20/0.47  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('49', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('50', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.20/0.47  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('53', plain,
% 0.20/0.47      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.47        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.47  thf('54', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('55', plain, ((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.47  thf('56', plain, ((v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '55'])).
% 0.20/0.47  thf('57', plain, ($false), inference('demod', [status(thm)], ['8', '56'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
