%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SnsFfVrXjm

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 167 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  527 (2749 expanded)
%              Number of equality atoms :   15 (  93 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0
        = ( u1_struct_0 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(t51_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v3_tex_2 @ C @ A )
                <=> ( v4_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( X4
       != ( u1_struct_0 @ X2 ) )
      | ~ ( v3_tex_2 @ X4 @ X3 )
      | ( v4_tex_2 @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t51_tex_2])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v4_tex_2 @ X2 @ X3 )
      | ~ ( v3_tex_2 @ ( u1_struct_0 @ X2 ) @ X3 )
      | ~ ( m1_pre_topc @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v3_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( v4_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v3_tex_2 @ sk_B @ X0 )
      | ( v4_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v4_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X5: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X5 ) )
      | ~ ( v4_tex_2 @ X5 @ sk_A )
      | ~ ( m1_pre_topc @ X5 @ sk_A )
      | ~ ( v1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
     != ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v1_pre_topc @ ( sk_C @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['33','34'])).

thf('51',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('52',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['40','49','50','51'])).

thf('53',plain,(
    v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['8','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SnsFfVrXjm
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 24 iterations in 0.017s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.47  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.47  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.47  thf(t53_tex_2, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47           ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.22/0.47                ( ![C:$i]:
% 0.22/0.47                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.22/0.47                      ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.47                    ( ~( ( v4_tex_2 @ C @ A ) & ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.47            ( l1_pre_topc @ A ) ) =>
% 0.22/0.47          ( ![B:$i]:
% 0.22/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.47                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47              ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.22/0.47                   ( ![C:$i]:
% 0.22/0.47                     ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.22/0.47                         ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.47                       ( ~( ( v4_tex_2 @ C @ A ) & 
% 0.22/0.47                            ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t53_tex_2])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t10_tsep_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47           ( ?[C:$i]:
% 0.22/0.47             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.22/0.47               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ X0)
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.22/0.47          | ~ (v2_struct_0 @ (sk_C @ X0 @ X1))
% 0.22/0.47          | ~ (l1_pre_topc @ X1)
% 0.22/0.47          | (v2_struct_0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.47        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.22/0.47        | (v1_xboole_0 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.22/0.47        | (v1_xboole_0 @ sk_B))),
% 0.22/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.22/0.47      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf('7', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('8', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.22/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ X0)
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.22/0.47          | ((X0) = (u1_struct_0 @ (sk_C @ X0 @ X1)))
% 0.22/0.47          | ~ (l1_pre_topc @ X1)
% 0.22/0.47          | (v2_struct_0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.47        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.22/0.47        | (v1_xboole_0 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.47  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.22/0.47        | (v1_xboole_0 @ sk_B))),
% 0.22/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (((v1_xboole_0 @ sk_B) | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A))))),
% 0.22/0.47      inference('clc', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('18', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.22/0.47      inference('clc', [status(thm)], ['16', '17'])).
% 0.22/0.47  thf(t51_tex_2, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.47           ( ![C:$i]:
% 0.22/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.47                 ( ( v3_tex_2 @ C @ A ) <=> ( v4_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.47         (~ (m1_pre_topc @ X2 @ X3)
% 0.22/0.47          | ((X4) != (u1_struct_0 @ X2))
% 0.22/0.47          | ~ (v3_tex_2 @ X4 @ X3)
% 0.22/0.47          | (v4_tex_2 @ X2 @ X3)
% 0.22/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.22/0.47          | ~ (l1_pre_topc @ X3)
% 0.22/0.47          | (v2_struct_0 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t51_tex_2])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i]:
% 0.22/0.47         ((v2_struct_0 @ X3)
% 0.22/0.47          | ~ (l1_pre_topc @ X3)
% 0.22/0.47          | ~ (m1_subset_1 @ (u1_struct_0 @ X2) @ 
% 0.22/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.22/0.47          | (v4_tex_2 @ X2 @ X3)
% 0.22/0.47          | ~ (v3_tex_2 @ (u1_struct_0 @ X2) @ X3)
% 0.22/0.47          | ~ (m1_pre_topc @ X2 @ X3))),
% 0.22/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.47  thf('21', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.47          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.22/0.47          | ~ (v3_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ X0)
% 0.22/0.47          | (v4_tex_2 @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | (v2_struct_0 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['18', '20'])).
% 0.22/0.47  thf('22', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.22/0.47      inference('clc', [status(thm)], ['16', '17'])).
% 0.22/0.47  thf('23', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.47          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.22/0.47          | ~ (v3_tex_2 @ sk_B @ X0)
% 0.22/0.47          | (v4_tex_2 @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.22/0.47          | ~ (l1_pre_topc @ X0)
% 0.22/0.47          | (v2_struct_0 @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.47        | (v4_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.47        | ~ (v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.47        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['9', '23'])).
% 0.22/0.47  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('26', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('27', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('28', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ X0)
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.22/0.47          | (m1_pre_topc @ (sk_C @ X0 @ X1) @ X1)
% 0.22/0.47          | ~ (l1_pre_topc @ X1)
% 0.22/0.47          | (v2_struct_0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.47        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.47        | (v1_xboole_0 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.47  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('31', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.47        | (v1_xboole_0 @ sk_B))),
% 0.22/0.47      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.47  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('33', plain,
% 0.22/0.47      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.47      inference('clc', [status(thm)], ['31', '32'])).
% 0.22/0.47  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('35', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.47      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.47  thf('36', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A) | (v4_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['24', '25', '26', '35'])).
% 0.22/0.47  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('38', plain, ((v4_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.47      inference('clc', [status(thm)], ['36', '37'])).
% 0.22/0.47  thf('39', plain,
% 0.22/0.47      (![X5 : $i]:
% 0.22/0.47         (((sk_B) != (u1_struct_0 @ X5))
% 0.22/0.47          | ~ (v4_tex_2 @ X5 @ sk_A)
% 0.22/0.47          | ~ (m1_pre_topc @ X5 @ sk_A)
% 0.22/0.47          | ~ (v1_pre_topc @ X5)
% 0.22/0.47          | (v2_struct_0 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('40', plain,
% 0.22/0.47      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.22/0.47        | ~ (v1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.22/0.47        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.47        | ((sk_B) != (u1_struct_0 @ (sk_C @ sk_B @ sk_A))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.47  thf('41', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('42', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((v1_xboole_0 @ X0)
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.22/0.47          | (v1_pre_topc @ (sk_C @ X0 @ X1))
% 0.22/0.47          | ~ (l1_pre_topc @ X1)
% 0.22/0.47          | (v2_struct_0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.22/0.47  thf('43', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.47        | (v1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.22/0.47        | (v1_xboole_0 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.47  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('45', plain,
% 0.22/0.47      (((v2_struct_0 @ sk_A)
% 0.22/0.47        | (v1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.22/0.47        | (v1_xboole_0 @ sk_B))),
% 0.22/0.47      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.47  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('47', plain,
% 0.22/0.47      (((v1_xboole_0 @ sk_B) | (v1_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.22/0.47      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.47  thf('48', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('49', plain, ((v1_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.22/0.47      inference('clc', [status(thm)], ['47', '48'])).
% 0.22/0.47  thf('50', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.47      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.47  thf('51', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.22/0.47      inference('clc', [status(thm)], ['16', '17'])).
% 0.22/0.47  thf('52', plain,
% 0.22/0.47      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A)) | ((sk_B) != (sk_B)))),
% 0.22/0.47      inference('demod', [status(thm)], ['40', '49', '50', '51'])).
% 0.22/0.47  thf('53', plain, ((v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.22/0.47      inference('simplify', [status(thm)], ['52'])).
% 0.22/0.47  thf('54', plain, ($false), inference('demod', [status(thm)], ['8', '53'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
