%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.osli6ilYhW

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 302 expanded)
%              Number of leaves         :   20 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          :  588 (3742 expanded)
%              Number of equality atoms :   15 ( 139 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t28_compts_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( C = D )
                   => ( ( v2_compts_1 @ C @ A )
                    <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( C = D )
                     => ( ( v2_compts_1 @ C @ A )
                      <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_compts_1])).

thf('0',plain,
    ( ~ ( v2_compts_1 @ sk_D_1 @ sk_B )
    | ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_compts_1 @ sk_D_1 @ sk_B )
   <= ~ ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_B )
   <= ~ ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( v2_compts_1 @ sk_D_1 @ sk_B )
    | ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( v2_compts_1 @ sk_D_1 @ sk_B )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_compts_1 @ sk_D_1 @ sk_B )
   <= ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_compts_1 @ sk_C @ sk_B )
   <= ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) )
               => ( ( v2_compts_1 @ C @ A )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( D = C )
                       => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ ( k2_struct_0 @ X7 ) )
      | ( ( sk_D @ X9 @ X7 )
        = X9 )
      | ( v2_compts_1 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C @ sk_A )
      | ( ( sk_D @ sk_C @ X0 )
        = sk_C )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C @ sk_A )
      | ( ( sk_D @ sk_C @ X0 )
        = sk_C )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( sk_D @ sk_C @ sk_B )
      = sk_C )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( sk_D @ sk_C @ sk_B )
      = sk_C )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ( sk_D @ sk_C @ sk_B )
      = sk_C )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ ( k2_struct_0 @ X7 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X9 @ X7 ) @ X7 )
      | ( v2_compts_1 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ sk_B ) @ sk_B )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v2_compts_1 @ ( sk_D @ sk_C @ sk_B ) @ sk_B )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ~ ( v2_compts_1 @ sk_C @ sk_B )
      | ( v2_compts_1 @ sk_C @ sk_A ) )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_B )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_compts_1 @ sk_C @ sk_A )
    | ~ ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','45'])).

thf('47',plain,(
    ~ ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['4','46'])).

thf('48',plain,(
    ~ ( v2_compts_1 @ sk_C @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['3','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ ( k2_struct_0 @ X7 ) )
      | ~ ( v2_compts_1 @ X9 @ X8 )
      | ( X10 != X9 )
      | ( v2_compts_1 @ X10 @ X7 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v2_compts_1 @ X9 @ X7 )
      | ~ ( v2_compts_1 @ X9 @ X8 )
      | ~ ( r1_tarski @ X9 @ ( k2_struct_0 @ X7 ) )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_C @ sk_A )
      | ( v2_compts_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_C @ sk_A )
      | ( v2_compts_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_compts_1 @ sk_C @ sk_A )
   <= ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('57',plain,
    ( ( v2_compts_1 @ sk_C @ sk_A )
    | ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('58',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','46','57'])).

thf('59',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ( v2_compts_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['55','59'])).

thf('61',plain,
    ( ( v2_compts_1 @ sk_C @ sk_B )
    | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,(
    r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('63',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_compts_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['48','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.osli6ilYhW
% 0.12/0.35  % Computer   : n006.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 18:27:22 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 89 iterations in 0.044s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(t28_compts_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                   ( ( ( C ) = ( D ) ) =>
% 0.21/0.51                     ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( l1_pre_topc @ A ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                      ( ( ( C ) = ( D ) ) =>
% 0.21/0.51                        ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t28_compts_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((~ (v2_compts_1 @ sk_D_1 @ sk_B) | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((~ (v2_compts_1 @ sk_D_1 @ sk_B)) <= (~ ((v2_compts_1 @ sk_D_1 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((~ (v2_compts_1 @ sk_C @ sk_B)) <= (~ ((v2_compts_1 @ sk_D_1 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (~ ((v2_compts_1 @ sk_D_1 @ sk_B)) | ~ ((v2_compts_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((v2_compts_1 @ sk_D_1 @ sk_B) | (v2_compts_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((v2_compts_1 @ sk_D_1 @ sk_B)) <= (((v2_compts_1 @ sk_D_1 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['5'])).
% 0.21/0.51  thf('7', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((v2_compts_1 @ sk_C @ sk_B)) <= (((v2_compts_1 @ sk_D_1 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf(d3_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X3 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain, (((sk_C) = (sk_D_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('14', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (((r1_tarski @ sk_C @ (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['9', '14'])).
% 0.21/0.51  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('21', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain, ((r1_tarski @ sk_C @ (k2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t11_compts_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 0.21/0.51                 ( ( v2_compts_1 @ C @ A ) <=>
% 0.21/0.51                   ( ![D:$i]:
% 0.21/0.51                     ( ( m1_subset_1 @
% 0.21/0.51                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.51          | ~ (r1_tarski @ X9 @ (k2_struct_0 @ X7))
% 0.21/0.51          | ((sk_D @ X9 @ X7) = (X9))
% 0.21/0.51          | (v2_compts_1 @ X9 @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.51          | ~ (l1_pre_topc @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | (v2_compts_1 @ sk_C @ sk_A)
% 0.21/0.51          | ((sk_D @ sk_C @ X0) = (sk_C))
% 0.21/0.51          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_compts_1 @ sk_C @ sk_A)
% 0.21/0.51          | ((sk_D @ sk_C @ X0) = (sk_C))
% 0.21/0.51          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.51        | ((sk_D @ sk_C @ sk_B) = (sk_C))
% 0.21/0.51        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '28'])).
% 0.21/0.51  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((((sk_D @ sk_C @ sk_B) = (sk_C)) | (v2_compts_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((~ (v2_compts_1 @ sk_C @ sk_A)) <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((((sk_D @ sk_C @ sk_B) = (sk_C))) <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain, ((r1_tarski @ sk_C @ (k2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '22'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.51          | ~ (r1_tarski @ X9 @ (k2_struct_0 @ X7))
% 0.21/0.51          | ~ (v2_compts_1 @ (sk_D @ X9 @ X7) @ X7)
% 0.21/0.51          | (v2_compts_1 @ X9 @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.51          | ~ (l1_pre_topc @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | (v2_compts_1 @ sk_C @ sk_A)
% 0.21/0.51          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 0.21/0.51          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_compts_1 @ sk_C @ sk_A)
% 0.21/0.51          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 0.21/0.51          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.51        | ~ (v2_compts_1 @ (sk_D @ sk_C @ sk_B) @ sk_B)
% 0.21/0.51        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '39'])).
% 0.21/0.51  thf('41', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((~ (v2_compts_1 @ (sk_D @ sk_C @ sk_B) @ sk_B)
% 0.21/0.51        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((~ (v2_compts_1 @ sk_C @ sk_B) | (v2_compts_1 @ sk_C @ sk_A)))
% 0.21/0.51         <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      ((~ (v2_compts_1 @ sk_C @ sk_A)) <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((~ (v2_compts_1 @ sk_C @ sk_B)) <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((v2_compts_1 @ sk_C @ sk_A)) | ~ ((v2_compts_1 @ sk_D_1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '45'])).
% 0.21/0.51  thf('47', plain, (~ ((v2_compts_1 @ sk_D_1 @ sk_B))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['4', '46'])).
% 0.21/0.51  thf('48', plain, (~ (v2_compts_1 @ sk_C @ sk_B)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['3', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.51          | ~ (r1_tarski @ X9 @ (k2_struct_0 @ X7))
% 0.21/0.51          | ~ (v2_compts_1 @ X9 @ X8)
% 0.21/0.51          | ((X10) != (X9))
% 0.21/0.51          | (v2_compts_1 @ X10 @ X7)
% 0.21/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.51          | ~ (l1_pre_topc @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.51          | (v2_compts_1 @ X9 @ X7)
% 0.21/0.51          | ~ (v2_compts_1 @ X9 @ X8)
% 0.21/0.51          | ~ (r1_tarski @ X9 @ (k2_struct_0 @ X7))
% 0.21/0.51          | ~ (m1_pre_topc @ X7 @ X8))),
% 0.21/0.51      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.21/0.51          | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.21/0.51          | (v2_compts_1 @ sk_C @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '52'])).
% 0.21/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.21/0.51          | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.21/0.51          | (v2_compts_1 @ sk_C @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (((v2_compts_1 @ sk_C @ sk_A)) <= (((v2_compts_1 @ sk_C @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['5'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (((v2_compts_1 @ sk_C @ sk_A)) | ((v2_compts_1 @ sk_D_1 @ sk_B))),
% 0.21/0.51      inference('split', [status(esa)], ['5'])).
% 0.21/0.51  thf('58', plain, (((v2_compts_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['4', '46', '57'])).
% 0.21/0.51  thf('59', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['56', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.21/0.51          | (v2_compts_1 @ sk_C @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['55', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (((v2_compts_1 @ sk_C @ sk_B)
% 0.21/0.51        | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ sk_B))
% 0.21/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '60'])).
% 0.21/0.51  thf('62', plain, ((r1_tarski @ sk_C @ (k2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '22'])).
% 0.21/0.51  thf('63', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain, ((v2_compts_1 @ sk_C @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.51  thf('65', plain, ($false), inference('demod', [status(thm)], ['48', '64'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
