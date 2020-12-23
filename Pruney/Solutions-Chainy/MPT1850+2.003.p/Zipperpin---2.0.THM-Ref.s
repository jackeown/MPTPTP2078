%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.03RV0hVcC4

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 561 expanded)
%              Number of leaves         :   29 ( 172 expanded)
%              Depth                    :   22
%              Number of atoms          : 1323 (6439 expanded)
%              Number of equality atoms :   24 ( 204 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t17_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v1_tdlat_3 @ A ) )
           => ( v1_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v1_tdlat_3 @ A ) )
             => ( v1_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tex_2])).

thf('4',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t31_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ( r1_tarski @ X19 @ ( u1_pre_topc @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('24',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t35_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v1_tops_2 @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                   => ( ( D = B )
                     => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_tops_2 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ( v1_tops_2 @ X17 @ X18 )
      | ( X17 != X15 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v1_tops_2 @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('33',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('52',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( r1_tarski @ X19 @ ( u1_pre_topc @ X20 ) )
      | ( v1_tops_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['57','58','60'])).

thf('62',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['28','29','30','39','61'])).

thf('63',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['22','62'])).

thf('64',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_B )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ( r1_tarski @ X19 @ ( u1_pre_topc @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('77',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('78',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v1_tops_2 @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ sk_B )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('84',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('86',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('88',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( r1_tarski @ X19 @ ( u1_pre_topc @ X20 ) )
      | ( v1_tops_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('96',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['80','81','82','83','96'])).

thf('98',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['75','97'])).

thf('99',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['65','98'])).

thf(d1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('100',plain,(
    ! [X26: $i] :
      ( ~ ( v1_tdlat_3 @ X26 )
      | ( ( u1_pre_topc @ X26 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('101',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('102',plain,(
    m1_pre_topc @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('103',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('106',plain,(
    ! [X25: $i] :
      ( ~ ( v1_tdlat_3 @ X25 )
      | ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('107',plain,
    ( ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['104','109','110'])).

thf('112',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','111'])).

thf('113',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('114',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('118',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('119',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('124',plain,(
    ! [X6: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('125',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t58_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
       => ( v2_pre_topc @ A ) ) ) )).

thf('126',plain,(
    ! [X7: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t58_pre_topc])).

thf('127',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(demod,[status(thm)],['107','108'])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('135',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123','133','134'])).

thf('136',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','135'])).

thf('137',plain,(
    ! [X26: $i] :
      ( ( ( u1_pre_topc @ X26 )
       != ( k9_setfam_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_tdlat_3 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('138',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v1_tdlat_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ( u1_pre_topc @ sk_B )
 != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ( u1_pre_topc @ sk_B )
 != ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['99','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.03RV0hVcC4
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:07:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 109 iterations in 0.050s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.50  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(t2_tsep_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.50  thf(t65_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.50             ( m1_pre_topc @
% 0.20/0.50               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X10)
% 0.20/0.50          | ~ (m1_pre_topc @ X11 @ X10)
% 0.20/0.50          | (m1_pre_topc @ X11 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.20/0.50          | ~ (l1_pre_topc @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (m1_pre_topc @ X0 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_pre_topc @ X0 @ 
% 0.20/0.50           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf(t17_tex_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.50                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.50               ( v1_tdlat_3 @ A ) ) =>
% 0.20/0.50             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( l1_pre_topc @ A ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( l1_pre_topc @ B ) =>
% 0.20/0.50              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.50                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.50                  ( v1_tdlat_3 @ A ) ) =>
% 0.20/0.50                ( v1_tdlat_3 @ B ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t17_tex_2])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t59_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_pre_topc @
% 0.20/0.50             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.50           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X8 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.20/0.50          | (m1_pre_topc @ X8 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | (m1_pre_topc @ X0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.50          | (m1_pre_topc @ X0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.50  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf(dt_u1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( m1_subset_1 @
% 0.20/0.50         ( u1_pre_topc @ A ) @ 
% 0.20/0.50         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X5 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.50          | ~ (l1_pre_topc @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.50  thf(t31_tops_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @
% 0.20/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.50               ( m1_subset_1 @
% 0.20/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.50          | (m1_subset_1 @ X14 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.20/0.50          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.20/0.50          | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t31_tops_2])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X1)
% 0.20/0.50          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.50  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.50  thf(t78_tops_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @
% 0.20/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X19 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.20/0.50          | ~ (v1_tops_2 @ X19 @ X20)
% 0.20/0.50          | (r1_tarski @ X19 @ (u1_pre_topc @ X20))
% 0.20/0.50          | ~ (l1_pre_topc @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.20/0.50        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.20/0.50        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X5 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.50          | ~ (l1_pre_topc @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.50  thf(t35_tops_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @
% 0.20/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.50               ( ( v1_tops_2 @ B @ A ) =>
% 0.20/0.50                 ( ![D:$i]:
% 0.20/0.50                   ( ( m1_subset_1 @
% 0.20/0.50                       D @ 
% 0.20/0.50                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.20/0.50                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X15 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.20/0.50          | ~ (v1_tops_2 @ X15 @ X16)
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ 
% 0.20/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.20/0.50          | (v1_tops_2 @ X17 @ X18)
% 0.20/0.50          | ((X17) != (X15))
% 0.20/0.50          | ~ (m1_pre_topc @ X18 @ X16)
% 0.20/0.50          | ~ (l1_pre_topc @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X16)
% 0.20/0.50          | ~ (m1_pre_topc @ X18 @ X16)
% 0.20/0.50          | (v1_tops_2 @ X15 @ X18)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.20/0.50          | ~ (v1_tops_2 @ X15 @ X16)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.50          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0)
% 0.20/0.50          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.50        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.20/0.50        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '27'])).
% 0.20/0.50  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_pre_topc @ X0 @ 
% 0.20/0.50           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((m1_pre_topc @ sk_B @ 
% 0.20/0.50         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((m1_pre_topc @ sk_B @ 
% 0.20/0.50        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X8 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.20/0.50          | (m1_pre_topc @ X8 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.50  thf('37', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X10)
% 0.20/0.50          | ~ (m1_pre_topc @ X11 @ X10)
% 0.20/0.50          | (m1_pre_topc @ X11 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.20/0.50          | ~ (l1_pre_topc @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (m1_pre_topc @ sk_A @ 
% 0.20/0.50           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((m1_pre_topc @ sk_A @ 
% 0.20/0.50        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X8 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.20/0.50          | (m1_pre_topc @ X8 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.50  thf('48', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('50', plain, ((m1_pre_topc @ sk_A @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X1)
% 0.20/0.50          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X19 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.20/0.50          | ~ (r1_tarski @ X19 @ (u1_pre_topc @ X20))
% 0.20/0.50          | (v1_tops_2 @ X19 @ X20)
% 0.20/0.50          | ~ (l1_pre_topc @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.20/0.50        | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.50      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.50  thf('61', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['57', '58', '60'])).
% 0.20/0.50  thf('62', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29', '30', '39', '61'])).
% 0.20/0.50  thf('63', plain, ((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X0 : $i, X2 : $i]:
% 0.20/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      ((~ (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.50        | ((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf('66', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X1)
% 0.20/0.50          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X19 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.20/0.50          | ~ (v1_tops_2 @ X19 @ X20)
% 0.20/0.50          | (r1_tarski @ X19 @ (u1_pre_topc @ X20))
% 0.20/0.50          | ~ (l1_pre_topc @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.50        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.50  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.50        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      (![X5 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.50          | ~ (l1_pre_topc @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X16)
% 0.20/0.50          | ~ (m1_pre_topc @ X18 @ X16)
% 0.20/0.50          | (v1_tops_2 @ X15 @ X18)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.20/0.50          | ~ (v1_tops_2 @ X15 @ X16)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.50          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ X0)
% 0.20/0.50          | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | ~ (m1_pre_topc @ sk_A @ sk_B)
% 0.20/0.50        | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)
% 0.20/0.50        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['76', '79'])).
% 0.20/0.50  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('83', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      ((m1_pre_topc @ sk_B @ 
% 0.20/0.50        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.50          | (m1_pre_topc @ X0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('86', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X1)
% 0.20/0.50          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.50  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X19 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.20/0.50          | ~ (r1_tarski @ X19 @ (u1_pre_topc @ X20))
% 0.20/0.50          | (v1_tops_2 @ X19 @ X20)
% 0.20/0.50          | ~ (l1_pre_topc @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B)
% 0.20/0.50        | ~ (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.50  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('95', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.50      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.50  thf('96', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.20/0.50  thf('97', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['80', '81', '82', '83', '96'])).
% 0.20/0.50  thf('98', plain, ((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['75', '97'])).
% 0.20/0.50  thf('99', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['65', '98'])).
% 0.20/0.50  thf(d1_tdlat_3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ( v1_tdlat_3 @ A ) <=>
% 0.20/0.50         ( ( u1_pre_topc @ A ) = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      (![X26 : $i]:
% 0.20/0.50         (~ (v1_tdlat_3 @ X26)
% 0.20/0.50          | ((u1_pre_topc @ X26) = (k9_setfam_1 @ (u1_struct_0 @ X26)))
% 0.20/0.50          | ~ (l1_pre_topc @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.20/0.50  thf('101', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('102', plain, ((m1_pre_topc @ sk_A @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf(t4_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.50               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.20/0.50                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.50  thf('103', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.50          | ~ (m1_pre_topc @ X22 @ X24)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X24))
% 0.20/0.50          | ~ (m1_pre_topc @ X24 @ X23)
% 0.20/0.50          | ~ (l1_pre_topc @ X23)
% 0.20/0.50          | ~ (v2_pre_topc @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.50  thf('104', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ sk_A @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.50  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_tdlat_3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) => ( ( v1_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.20/0.50  thf('106', plain,
% 0.20/0.50      (![X25 : $i]:
% 0.20/0.50         (~ (v1_tdlat_3 @ X25) | (v2_pre_topc @ X25) | ~ (l1_pre_topc @ X25))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_tdlat_3])).
% 0.20/0.50  thf('107', plain, (((v2_pre_topc @ sk_A) | ~ (v1_tdlat_3 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.50  thf('108', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['107', '108'])).
% 0.20/0.50  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('111', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ sk_A @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['104', '109', '110'])).
% 0.20/0.50  thf('112', plain,
% 0.20/0.50      ((~ (m1_pre_topc @ sk_A @ sk_B)
% 0.20/0.50        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['101', '111'])).
% 0.20/0.50  thf('113', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('114', plain,
% 0.20/0.50      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['112', '113'])).
% 0.20/0.50  thf('115', plain,
% 0.20/0.50      (![X0 : $i, X2 : $i]:
% 0.20/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('116', plain,
% 0.20/0.50      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.50  thf('117', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('118', plain,
% 0.20/0.50      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.50  thf('119', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.50          | ~ (m1_pre_topc @ X22 @ X24)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X24))
% 0.20/0.50          | ~ (m1_pre_topc @ X24 @ X23)
% 0.20/0.50          | ~ (l1_pre_topc @ X23)
% 0.20/0.50          | ~ (v2_pre_topc @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.50  thf('120', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['118', '119'])).
% 0.20/0.50  thf('121', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['120'])).
% 0.20/0.50  thf('122', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50        | ~ (m1_pre_topc @ sk_A @ sk_B)
% 0.20/0.50        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['117', '121'])).
% 0.20/0.50  thf('123', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(fc6_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ( v1_pre_topc @
% 0.20/0.50           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.20/0.50         ( v2_pre_topc @
% 0.20/0.50           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.50  thf('124', plain,
% 0.20/0.50      (![X6 : $i]:
% 0.20/0.50         ((v2_pre_topc @ 
% 0.20/0.50           (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.20/0.50          | ~ (l1_pre_topc @ X6)
% 0.20/0.50          | ~ (v2_pre_topc @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.20/0.50  thf('125', plain,
% 0.20/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t58_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ( v2_pre_topc @
% 0.20/0.50           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.50         ( v2_pre_topc @ A ) ) ))).
% 0.20/0.50  thf('126', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         (~ (v2_pre_topc @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.20/0.50          | (v2_pre_topc @ X7)
% 0.20/0.50          | ~ (l1_pre_topc @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t58_pre_topc])).
% 0.20/0.50  thf('127', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ 
% 0.20/0.50           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | (v2_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['125', '126'])).
% 0.20/0.50  thf('128', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('129', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ 
% 0.20/0.50           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.50        | (v2_pre_topc @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['127', '128'])).
% 0.20/0.50  thf('130', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['124', '129'])).
% 0.20/0.50  thf('131', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['107', '108'])).
% 0.20/0.50  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('133', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.20/0.50  thf('134', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('135', plain,
% 0.20/0.50      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['122', '123', '133', '134'])).
% 0.20/0.50  thf('136', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['116', '135'])).
% 0.20/0.50  thf('137', plain,
% 0.20/0.50      (![X26 : $i]:
% 0.20/0.50         (((u1_pre_topc @ X26) != (k9_setfam_1 @ (u1_struct_0 @ X26)))
% 0.20/0.50          | (v1_tdlat_3 @ X26)
% 0.20/0.50          | ~ (l1_pre_topc @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.20/0.50  thf('138', plain,
% 0.20/0.50      ((((u1_pre_topc @ sk_B) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | (v1_tdlat_3 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['136', '137'])).
% 0.20/0.50  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('140', plain,
% 0.20/0.50      ((((u1_pre_topc @ sk_B) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | (v1_tdlat_3 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['138', '139'])).
% 0.20/0.50  thf('141', plain, (~ (v1_tdlat_3 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('142', plain,
% 0.20/0.50      (((u1_pre_topc @ sk_B) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['140', '141'])).
% 0.20/0.50  thf('143', plain,
% 0.20/0.50      ((((u1_pre_topc @ sk_B) != (u1_pre_topc @ sk_A))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v1_tdlat_3 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['100', '142'])).
% 0.20/0.50  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('145', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('146', plain, (((u1_pre_topc @ sk_B) != (u1_pre_topc @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.20/0.50  thf('147', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['99', '146'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
