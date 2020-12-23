%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NfB4WZMB5M

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 (1057 expanded)
%              Number of leaves         :   20 ( 287 expanded)
%              Depth                    :   21
%              Number of atoms          :  866 (11930 expanded)
%              Number of equality atoms :   34 ( 288 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( v1_subset_1 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('2',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t27_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v1_tdlat_3 @ X12 )
      | ( v2_tex_2 @ X11 @ X12 )
      | ( X11
       != ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('8',plain,(
    ! [X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X12 ) @ X12 )
      | ~ ( v1_tdlat_3 @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X12 ) @ X12 )
      | ~ ( v1_tdlat_3 @ X12 ) ) ),
    inference(demod,[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('15',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_tex_2 @ X8 @ X9 )
      | ~ ( v2_tex_2 @ X10 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf('28',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_subset_1 @ X7 @ X6 )
      | ( X7 != X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('37',plain,(
    ! [X6: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( v1_subset_1 @ X6 @ X6 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ X6 @ X6 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['6','40'])).

thf('42',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( sk_C @ X8 @ X9 ) )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('48',plain,(
    ! [X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X12 ) @ X12 )
      | ~ ( v1_tdlat_3 @ X12 ) ) ),
    inference(demod,[status(thm)],['8','12'])).

thf('49',plain,
    ( ( ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( v2_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['6','40'])).

thf('54',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','41'])).

thf('58',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','41'])).

thf('59',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','41'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','56','57','58','59','60'])).

thf('62',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('63',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('64',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','40','63'])).

thf('65',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['62','64'])).

thf('66',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['61','65'])).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_C @ sk_B @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('70',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('71',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_tex_2 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ( v3_tex_2 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
        | ~ ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ~ ( v2_tex_2 @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['54','55'])).

thf('78',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['6','40'])).

thf('80',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['62','64'])).

thf('82',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['68','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( X8
       != ( sk_C @ X8 @ X9 ) )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['54','55'])).

thf('92',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['62','64'])).

thf('94',plain,(
    sk_B
 != ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['85','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NfB4WZMB5M
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:16:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 84 iterations in 0.041s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.50  thf(t49_tex_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.22/0.50         ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.50             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50              ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.50                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d7_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         (((X7) = (X6))
% 0.22/0.50          | (v1_subset_1 @ X7 @ X6)
% 0.22/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.22/0.50       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf(t27_tex_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 0.22/0.50             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.50          | ~ (v1_tdlat_3 @ X12)
% 0.22/0.50          | (v2_tex_2 @ X11 @ X12)
% 0.22/0.50          | ((X11) != (u1_struct_0 @ X12))
% 0.22/0.50          | ~ (l1_pre_topc @ X12)
% 0.22/0.50          | (v2_struct_0 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [t27_tex_2])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X12 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X12)
% 0.22/0.50          | ~ (l1_pre_topc @ X12)
% 0.22/0.50          | (v2_tex_2 @ (u1_struct_0 @ X12) @ X12)
% 0.22/0.50          | ~ (v1_tdlat_3 @ X12)
% 0.22/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.22/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X3 : $i, X5 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('12', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X12 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X12)
% 0.22/0.50          | ~ (l1_pre_topc @ X12)
% 0.22/0.50          | (v2_tex_2 @ (u1_struct_0 @ X12) @ X12)
% 0.22/0.50          | ~ (v1_tdlat_3 @ X12))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '12'])).
% 0.22/0.50  thf('14', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d7_tex_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.50             ( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.50               ( ![C:$i]:
% 0.22/0.50                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.50                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.50          | ~ (v3_tex_2 @ X8 @ X9)
% 0.22/0.50          | ~ (v2_tex_2 @ X10 @ X9)
% 0.22/0.50          | ~ (r1_tarski @ X8 @ X10)
% 0.22/0.50          | ((X8) = (X10))
% 0.22/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.50          | ~ (l1_pre_topc @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ sk_A)
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50          | ((sk_B) = (X0))
% 0.22/0.50          | ~ (r1_tarski @ sk_B @ X0)
% 0.22/0.50          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.50          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50          | ((sk_B) = (X0))
% 0.22/0.50          | ~ (r1_tarski @ sk_B @ X0)
% 0.22/0.50          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.50          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.50           | ~ (r1_tarski @ sk_B @ X0)
% 0.22/0.50           | ((sk_B) = (X0))
% 0.22/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.22/0.50         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.22/0.50         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.50         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.22/0.50         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('25', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.22/0.50         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.22/0.50         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (((~ (v1_tdlat_3 @ sk_A)
% 0.22/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '26'])).
% 0.22/0.50  thf('28', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.22/0.50         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.22/0.50  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.22/0.50         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('split', [status(esa)], ['33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (((v1_subset_1 @ sk_B @ sk_B))
% 0.22/0.50         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.22/0.50             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['32', '34'])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (v1_subset_1 @ X7 @ X6)
% 0.22/0.50          | ((X7) != (X6))
% 0.22/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X6 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6)) | ~ (v1_subset_1 @ X6 @ X6))),
% 0.22/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.50  thf('38', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('39', plain, (![X6 : $i]: ~ (v1_subset_1 @ X6 @ X6)),
% 0.22/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.22/0.50       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '39'])).
% 0.22/0.50  thf('41', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['6', '40'])).
% 0.22/0.50  thf('42', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['5', '41'])).
% 0.22/0.50  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.50          | ~ (v2_tex_2 @ X8 @ X9)
% 0.22/0.50          | (r1_tarski @ X8 @ (sk_C @ X8 @ X9))
% 0.22/0.50          | (v3_tex_2 @ X8 @ X9)
% 0.22/0.50          | ~ (l1_pre_topc @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.50          | (r1_tarski @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.22/0.50          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      ((~ (v2_tex_2 @ sk_B @ sk_A)
% 0.22/0.50        | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.50           (sk_C @ (u1_struct_0 @ sk_A) @ sk_A))
% 0.22/0.50        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['42', '45'])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X12 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X12)
% 0.22/0.50          | ~ (l1_pre_topc @ X12)
% 0.22/0.50          | (v2_tex_2 @ (u1_struct_0 @ X12) @ X12)
% 0.22/0.50          | ~ (v1_tdlat_3 @ X12))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '12'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      ((((v2_tex_2 @ sk_B @ sk_A)
% 0.22/0.50         | ~ (v1_tdlat_3 @ sk_A)
% 0.22/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['47', '48'])).
% 0.22/0.50  thf('50', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      ((((v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.22/0.50  thf('53', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['6', '40'])).
% 0.22/0.50  thf('54', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['52', '53'])).
% 0.22/0.50  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('56', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['54', '55'])).
% 0.22/0.50  thf('57', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['5', '41'])).
% 0.22/0.50  thf('58', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['5', '41'])).
% 0.22/0.50  thf('59', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['5', '41'])).
% 0.22/0.50  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      (((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['46', '56', '57', '58', '59', '60'])).
% 0.22/0.50  thf('62', plain,
% 0.22/0.50      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['33'])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.22/0.50       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['33'])).
% 0.22/0.50  thf('64', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['6', '40', '63'])).
% 0.22/0.50  thf('65', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['62', '64'])).
% 0.22/0.50  thf('66', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['61', '65'])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i]:
% 0.22/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      ((~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.22/0.50        | ((sk_C @ sk_B @ sk_A) = (sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.50  thf('69', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('70', plain,
% 0.22/0.50      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.50  thf('71', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.50          | ~ (v2_tex_2 @ X8 @ X9)
% 0.22/0.50          | (m1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.50          | (v3_tex_2 @ X8 @ X9)
% 0.22/0.50          | ~ (l1_pre_topc @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.22/0.50           | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50           | (v3_tex_2 @ X0 @ sk_A)
% 0.22/0.50           | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ 
% 0.22/0.50              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50           | ~ (v2_tex_2 @ X0 @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.50  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.22/0.50           | (v3_tex_2 @ X0 @ sk_A)
% 0.22/0.50           | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.22/0.50           | ~ (v2_tex_2 @ X0 @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      (((~ (v2_tex_2 @ sk_B @ sk_A)
% 0.22/0.50         | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.22/0.50         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['69', '75'])).
% 0.22/0.50  thf('77', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['54', '55'])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      ((((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.22/0.50         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.22/0.50         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['76', '77'])).
% 0.22/0.50  thf('79', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['6', '40'])).
% 0.22/0.50  thf('80', plain,
% 0.22/0.50      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.22/0.50        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 0.22/0.50  thf('81', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['62', '64'])).
% 0.22/0.50  thf('82', plain,
% 0.22/0.50      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.50      inference('clc', [status(thm)], ['80', '81'])).
% 0.22/0.50  thf('83', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('84', plain, ((r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['82', '83'])).
% 0.22/0.50  thf('85', plain, (((sk_C @ sk_B @ sk_A) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['68', '84'])).
% 0.22/0.50  thf('86', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('87', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.50          | ~ (v2_tex_2 @ X8 @ X9)
% 0.22/0.50          | ((X8) != (sk_C @ X8 @ X9))
% 0.22/0.50          | (v3_tex_2 @ X8 @ X9)
% 0.22/0.50          | ~ (l1_pre_topc @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.50  thf('88', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.50        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.22/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['86', '87'])).
% 0.22/0.50  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('90', plain,
% 0.22/0.50      (((v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.50        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.22/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['88', '89'])).
% 0.22/0.50  thf('91', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['54', '55'])).
% 0.22/0.50  thf('92', plain,
% 0.22/0.50      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.50  thf('93', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['62', '64'])).
% 0.22/0.50  thf('94', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['92', '93'])).
% 0.22/0.50  thf('95', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['85', '94'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
