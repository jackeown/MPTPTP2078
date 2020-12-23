%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vAnpKYiztv

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:27 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 252 expanded)
%              Number of leaves         :   18 (  79 expanded)
%              Depth                    :   20
%              Number of atoms          :  603 (4223 expanded)
%              Number of equality atoms :   25 ( 144 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X3 @ X4 ) )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X3 @ X4 ) @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( u1_struct_0 @ X0 ) )
      | ( v4_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3
        = ( u1_struct_0 @ ( sk_C_1 @ X3 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['19','20','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = sk_B )
    | ( v4_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X5 ) )
      | ~ ( v4_tex_2 @ X5 @ sk_A )
      | ~ ( m1_pre_topc @ X5 @ sk_A )
      | ~ ( v1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
     != ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v1_pre_topc @ ( sk_C_1 @ X3 @ X4 ) )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('45',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('46',plain,
    ( ( ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['34','43','44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('49',plain,
    ( ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    = sk_B ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v3_tex_2 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( v4_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('51',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X5: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X5 ) )
      | ~ ( v4_tex_2 @ X5 @ sk_A )
      | ~ ( m1_pre_topc @ X5 @ sk_A )
      | ~ ( v1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
     != ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('61',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('62',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('63',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['8','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vAnpKYiztv
% 0.16/0.37  % Computer   : n005.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:06:33 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 28 iterations in 0.021s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.24/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.51  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.24/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.24/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.51  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.24/0.51  thf(t53_tex_2, conjecture,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.24/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.51           ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.24/0.51                ( ![C:$i]:
% 0.24/0.51                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.24/0.51                      ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.51                    ( ~( ( v4_tex_2 @ C @ A ) & ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i]:
% 0.24/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.51            ( l1_pre_topc @ A ) ) =>
% 0.24/0.51          ( ![B:$i]:
% 0.24/0.51            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.24/0.51                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.51              ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.24/0.51                   ( ![C:$i]:
% 0.24/0.51                     ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.24/0.51                         ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.51                       ( ~( ( v4_tex_2 @ C @ A ) & 
% 0.24/0.51                            ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t53_tex_2])).
% 0.24/0.51  thf('0', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t10_tsep_1, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.24/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.51           ( ?[C:$i]:
% 0.24/0.51             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.24/0.51               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X3 : $i, X4 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ X3)
% 0.24/0.51          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.24/0.51          | ~ (v2_struct_0 @ (sk_C_1 @ X3 @ X4))
% 0.24/0.51          | ~ (l1_pre_topc @ X4)
% 0.24/0.51          | (v2_struct_0 @ X4))),
% 0.24/0.51      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | (v1_xboole_0 @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.51  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | (v1_xboole_0 @ sk_B))),
% 0.24/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.24/0.51  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.24/0.51      inference('clc', [status(thm)], ['4', '5'])).
% 0.24/0.51  thf('7', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('8', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))),
% 0.24/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X3 : $i, X4 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ X3)
% 0.24/0.51          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.24/0.51          | (m1_pre_topc @ (sk_C_1 @ X3 @ X4) @ X4)
% 0.24/0.51          | ~ (l1_pre_topc @ X4)
% 0.24/0.51          | (v2_struct_0 @ X4))),
% 0.24/0.51      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51        | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.51        | (v1_xboole_0 @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.51  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.51        | (v1_xboole_0 @ sk_B))),
% 0.24/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.24/0.51  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.24/0.51      inference('clc', [status(thm)], ['13', '14'])).
% 0.24/0.51  thf('16', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('17', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.24/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.24/0.51  thf(d8_tex_2, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.51           ( ( v4_tex_2 @ B @ A ) <=>
% 0.24/0.51             ( ![C:$i]:
% 0.24/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.51                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.51          | ((sk_C @ X0 @ X1) = (u1_struct_0 @ X0))
% 0.24/0.51          | (v4_tex_2 @ X0 @ X1)
% 0.24/0.51          | ~ (l1_pre_topc @ X1)
% 0.24/0.51          | (v2_struct_0 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.24/0.51  thf('19', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51        | (v4_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.51        | ((sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.51            = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.51  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('21', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('22', plain,
% 0.24/0.51      (![X3 : $i, X4 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ X3)
% 0.24/0.51          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.24/0.51          | ((X3) = (u1_struct_0 @ (sk_C_1 @ X3 @ X4)))
% 0.24/0.51          | ~ (l1_pre_topc @ X4)
% 0.24/0.51          | (v2_struct_0 @ X4))),
% 0.24/0.51      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.24/0.51  thf('23', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 0.24/0.51        | (v1_xboole_0 @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.51  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('25', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 0.24/0.51        | (v1_xboole_0 @ sk_B))),
% 0.24/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.24/0.51  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('27', plain,
% 0.24/0.51      (((v1_xboole_0 @ sk_B)
% 0.24/0.51        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.24/0.51      inference('clc', [status(thm)], ['25', '26'])).
% 0.24/0.51  thf('28', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('29', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.24/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.24/0.51  thf('30', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | (v4_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.51        | ((sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) = (sk_B)))),
% 0.24/0.51      inference('demod', [status(thm)], ['19', '20', '29'])).
% 0.24/0.51  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('32', plain,
% 0.24/0.51      ((((sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) = (sk_B))
% 0.24/0.51        | (v4_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.24/0.51      inference('clc', [status(thm)], ['30', '31'])).
% 0.24/0.51  thf('33', plain,
% 0.24/0.51      (![X5 : $i]:
% 0.24/0.51         (((sk_B) != (u1_struct_0 @ X5))
% 0.24/0.51          | ~ (v4_tex_2 @ X5 @ sk_A)
% 0.24/0.51          | ~ (m1_pre_topc @ X5 @ sk_A)
% 0.24/0.51          | ~ (v1_pre_topc @ X5)
% 0.24/0.51          | (v2_struct_0 @ X5))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('34', plain,
% 0.24/0.51      ((((sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) = (sk_B))
% 0.24/0.51        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | ~ (v1_pre_topc @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.51        | ((sk_B) != (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.24/0.51  thf('35', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('36', plain,
% 0.24/0.51      (![X3 : $i, X4 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ X3)
% 0.24/0.51          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.24/0.51          | (v1_pre_topc @ (sk_C_1 @ X3 @ X4))
% 0.24/0.51          | ~ (l1_pre_topc @ X4)
% 0.24/0.51          | (v2_struct_0 @ X4))),
% 0.24/0.51      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.24/0.51  thf('37', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51        | (v1_pre_topc @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | (v1_xboole_0 @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.24/0.51  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('39', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A)
% 0.24/0.51        | (v1_pre_topc @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | (v1_xboole_0 @ sk_B))),
% 0.24/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.24/0.51  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('41', plain,
% 0.24/0.51      (((v1_xboole_0 @ sk_B) | (v1_pre_topc @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.24/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.24/0.51  thf('42', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('43', plain, ((v1_pre_topc @ (sk_C_1 @ sk_B @ sk_A))),
% 0.24/0.51      inference('clc', [status(thm)], ['41', '42'])).
% 0.24/0.51  thf('44', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.24/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.24/0.51  thf('45', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.24/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.24/0.51  thf('46', plain,
% 0.24/0.51      ((((sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) = (sk_B))
% 0.24/0.51        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | ((sk_B) != (sk_B)))),
% 0.24/0.51      inference('demod', [status(thm)], ['34', '43', '44', '45'])).
% 0.24/0.51  thf('47', plain,
% 0.24/0.51      (((v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | ((sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) = (sk_B)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.24/0.51  thf('48', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))),
% 0.24/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.24/0.51  thf('49', plain, (((sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) = (sk_B))),
% 0.24/0.51      inference('clc', [status(thm)], ['47', '48'])).
% 0.24/0.51  thf('50', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.51          | ~ (v3_tex_2 @ (sk_C @ X0 @ X1) @ X1)
% 0.24/0.51          | (v4_tex_2 @ X0 @ X1)
% 0.24/0.51          | ~ (l1_pre_topc @ X1)
% 0.24/0.51          | (v2_struct_0 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.24/0.51  thf('51', plain,
% 0.24/0.51      ((~ (v3_tex_2 @ sk_B @ sk_A)
% 0.24/0.51        | (v2_struct_0 @ sk_A)
% 0.24/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51        | (v4_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.51        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.24/0.51  thf('52', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('54', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.24/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.24/0.51  thf('55', plain,
% 0.24/0.51      (((v2_struct_0 @ sk_A) | (v4_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.24/0.51      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.24/0.51  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('57', plain, ((v4_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.24/0.51      inference('clc', [status(thm)], ['55', '56'])).
% 0.24/0.51  thf('58', plain,
% 0.24/0.51      (![X5 : $i]:
% 0.24/0.51         (((sk_B) != (u1_struct_0 @ X5))
% 0.24/0.51          | ~ (v4_tex_2 @ X5 @ sk_A)
% 0.24/0.51          | ~ (m1_pre_topc @ X5 @ sk_A)
% 0.24/0.51          | ~ (v1_pre_topc @ X5)
% 0.24/0.51          | (v2_struct_0 @ X5))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('59', plain,
% 0.24/0.51      (((v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | ~ (v1_pre_topc @ (sk_C_1 @ sk_B @ sk_A))
% 0.24/0.51        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.51        | ((sk_B) != (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.24/0.51  thf('60', plain, ((v1_pre_topc @ (sk_C_1 @ sk_B @ sk_A))),
% 0.24/0.51      inference('clc', [status(thm)], ['41', '42'])).
% 0.24/0.51  thf('61', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.24/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.24/0.51  thf('62', plain, (((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.24/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.24/0.51  thf('63', plain,
% 0.24/0.51      (((v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) | ((sk_B) != (sk_B)))),
% 0.24/0.51      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.24/0.51  thf('64', plain, ((v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))),
% 0.24/0.51      inference('simplify', [status(thm)], ['63'])).
% 0.24/0.51  thf('65', plain, ($false), inference('demod', [status(thm)], ['8', '64'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
