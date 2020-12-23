%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZVT9MfGplh

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 289 expanded)
%              Number of leaves         :   22 (  92 expanded)
%              Depth                    :   18
%              Number of atoms          :  609 (3498 expanded)
%              Number of equality atoms :   15 ( 112 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t14_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                    = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                  & ( v1_tex_2 @ B @ A ) )
               => ( v1_tex_2 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                    & ( v1_tex_2 @ B @ A ) )
                 => ( v1_tex_2 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( sk_C @ X12 @ X13 )
        = ( u1_struct_0 @ X12 ) )
      | ( v1_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( m1_pre_topc @ X9 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ( m1_pre_topc @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['17','22'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( r1_tarski @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('27',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('32',plain,
    ( ( m1_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('34',plain,(
    m1_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ( m1_pre_topc @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('38',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( r1_tarski @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('42',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','42'])).

thf('44',plain,
    ( ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','43'])).

thf('45',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( v1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( v1_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('48',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('59',plain,
    ( ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( v1_tex_2 @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ( v1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_tex_2 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['53','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZVT9MfGplh
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 78 iterations in 0.033s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(t14_tex_2, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.49               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.22/0.49                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.22/0.49                   ( v1_tex_2 @ B @ A ) ) =>
% 0.22/0.49                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( l1_pre_topc @ A ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49              ( ![C:$i]:
% 0.22/0.49                ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.49                  ( ( ( ( g1_pre_topc @
% 0.22/0.49                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.22/0.49                        ( g1_pre_topc @
% 0.22/0.49                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.22/0.49                      ( v1_tex_2 @ B @ A ) ) =>
% 0.22/0.49                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 0.22/0.49  thf('0', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d3_tex_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49           ( ( v1_tex_2 @ B @ A ) <=>
% 0.22/0.49             ( ![C:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.49                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X12 @ X13)
% 0.22/0.49          | ((sk_C @ X12 @ X13) = (u1_struct_0 @ X12))
% 0.22/0.49          | (v1_tex_2 @ X12 @ X13)
% 0.22/0.49          | ~ (l1_pre_topc @ X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.22/0.49        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t2_tsep_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X9 : $i]: ((m1_pre_topc @ X9 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.49  thf(t65_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_pre_topc @ B ) =>
% 0.22/0.49           ( ( m1_pre_topc @ A @ B ) <=>
% 0.22/0.49             ( m1_pre_topc @
% 0.22/0.49               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X7)
% 0.22/0.49          | ~ (m1_pre_topc @ X8 @ X7)
% 0.22/0.49          | (m1_pre_topc @ X8 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.22/0.49          | ~ (l1_pre_topc @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | (m1_pre_topc @ X0 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((m1_pre_topc @ X0 @ 
% 0.22/0.49           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.22/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t59_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @
% 0.22/0.49             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.22/0.49           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X5 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.22/0.49          | (m1_pre_topc @ X5 @ X6)
% 0.22/0.49          | ~ (l1_pre_topc @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X0 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49          | ~ (l1_pre_topc @ sk_C_1)
% 0.22/0.49          | (m1_pre_topc @ X0 @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_m1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.49  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X0 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49          | (m1_pre_topc @ X0 @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['10', '15'])).
% 0.22/0.49  thf('17', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_B @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '16'])).
% 0.22/0.49  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.49  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '22'])).
% 0.22/0.49  thf(t35_borsuk_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.49          | (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X11))
% 0.22/0.49          | ~ (l1_pre_topc @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.49        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i, X2 : $i]:
% 0.22/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))
% 0.22/0.49        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.22/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((m1_pre_topc @ X0 @ 
% 0.22/0.49           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (((m1_pre_topc @ sk_C_1 @ 
% 0.22/0.49         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_C_1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((m1_pre_topc @ sk_C_1 @ 
% 0.22/0.49        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X5 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.22/0.49          | (m1_pre_topc @ X5 @ X6)
% 0.22/0.49          | ~ (l1_pre_topc @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.22/0.49  thf('36', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_C_1 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.49  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('38', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.49          | (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X11))
% 0.22/0.49          | ~ (l1_pre_topc @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.49        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.49  thf('43', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['29', '42'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (((v1_tex_2 @ sk_C_1 @ sk_A)
% 0.22/0.49        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3', '43'])).
% 0.22/0.49  thf('45', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('46', plain, (((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['44', '45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X12 @ X13)
% 0.22/0.49          | ~ (v1_subset_1 @ (sk_C @ X12 @ X13) @ (u1_struct_0 @ X13))
% 0.22/0.49          | (v1_tex_2 @ X12 @ X13)
% 0.22/0.49          | ~ (l1_pre_topc @ X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.22/0.49        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.49  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('50', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | (v1_tex_2 @ sk_C_1 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.22/0.49  thf('52', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('53', plain,
% 0.22/0.49      (~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('clc', [status(thm)], ['51', '52'])).
% 0.22/0.49  thf('54', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X12 @ X13)
% 0.22/0.49          | (m1_subset_1 @ (sk_C @ X12 @ X13) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.49          | (v1_tex_2 @ X12 @ X13)
% 0.22/0.49          | ~ (l1_pre_topc @ X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.22/0.49        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_A) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.49  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('58', plain, (((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['44', '45'])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      (((v1_tex_2 @ sk_C_1 @ sk_A)
% 0.22/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.22/0.49  thf('60', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('61', plain,
% 0.22/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X12 @ X13)
% 0.22/0.49          | ~ (v1_tex_2 @ X12 @ X13)
% 0.22/0.49          | ((X14) != (u1_struct_0 @ X12))
% 0.22/0.49          | (v1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.22/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.49          | ~ (l1_pre_topc @ X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.49  thf('63', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X13)
% 0.22/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.22/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.49          | (v1_subset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X13))
% 0.22/0.49          | ~ (v1_tex_2 @ X12 @ X13)
% 0.22/0.49          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.22/0.49      inference('simplify', [status(thm)], ['62'])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.22/0.49        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.22/0.49        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['61', '63'])).
% 0.22/0.49  thf('65', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('66', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('68', plain,
% 0.22/0.49      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.22/0.49  thf('69', plain, ($false), inference('demod', [status(thm)], ['53', '68'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
