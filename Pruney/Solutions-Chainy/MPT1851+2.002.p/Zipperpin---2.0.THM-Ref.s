%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9mABWjdv9d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:59 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 873 expanded)
%              Number of leaves         :   25 ( 257 expanded)
%              Depth                    :   19
%              Number of atoms          : 1045 (9658 expanded)
%              Number of equality atoms :   26 ( 317 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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

thf(t18_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v2_tdlat_3 @ A ) )
           => ( v2_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v2_tdlat_3 @ A ) )
             => ( v2_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_tex_2])).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( r1_tarski @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('20',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( r1_tarski @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('33',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_tops_2 @ X22 @ X23 )
      | ( r1_tarski @ X22 @ ( u1_pre_topc @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('41',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_tops_2 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ( v1_tops_2 @ X20 @ X21 )
      | ( X20 != X18 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('43',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( v1_tops_2 @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_tops_2 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ sk_B )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('49',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( r1_tarski @ X22 @ ( u1_pre_topc @ X23 ) )
      | ( v1_tops_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v1_tops_2 @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['55','57'])).

thf('59',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['45','46','47','48','58'])).

thf('60',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['39','59'])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('63',plain,(
    ! [X33: $i] :
      ( ~ ( v2_tdlat_3 @ X33 )
      | ( ( u1_pre_topc @ X33 )
        = ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('65',plain,(
    ! [X33: $i] :
      ( ( ( u1_pre_topc @ X33 )
       != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ X33 ) ) )
      | ( v2_tdlat_3 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_tdlat_3])).

thf('66',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_tdlat_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ( u1_pre_topc @ sk_B )
 != ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ( u1_pre_topc @ sk_B )
 != ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('77',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t31_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('78',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_2])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('86',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_tops_2 @ X22 @ X23 )
      | ( r1_tarski @ X22 @ ( u1_pre_topc @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( v1_tops_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( v1_tops_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('92',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('94',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( v1_tops_2 @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_tops_2 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_tops_2 @ X0 @ X1 )
      | ( v1_tops_2 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('100',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( r1_tarski @ X22 @ ( u1_pre_topc @ X23 ) )
      | ( v1_tops_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('104',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['97','98','104','105','106'])).

thf('108',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['90','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['75','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9mABWjdv9d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 445 iterations in 0.287s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.74  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.55/0.74  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.55/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.55/0.74  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.74  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(t2_tsep_1, axiom,
% 0.55/0.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.55/0.74  thf(t65_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( l1_pre_topc @ B ) =>
% 0.55/0.74           ( ( m1_pre_topc @ A @ B ) <=>
% 0.55/0.74             ( m1_pre_topc @
% 0.55/0.74               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X13)
% 0.55/0.74          | ~ (m1_pre_topc @ X14 @ X13)
% 0.55/0.74          | (m1_pre_topc @ X14 @ 
% 0.55/0.74             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.55/0.74          | ~ (l1_pre_topc @ X14))),
% 0.55/0.74      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0)
% 0.55/0.74          | (m1_pre_topc @ X0 @ 
% 0.55/0.74             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((m1_pre_topc @ X0 @ 
% 0.55/0.74           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['2'])).
% 0.55/0.74  thf(t18_tex_2, conjecture,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( l1_pre_topc @ B ) =>
% 0.55/0.74           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.55/0.74                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.55/0.74               ( v2_tdlat_3 @ A ) ) =>
% 0.55/0.74             ( v2_tdlat_3 @ B ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i]:
% 0.55/0.74        ( ( l1_pre_topc @ A ) =>
% 0.55/0.74          ( ![B:$i]:
% 0.55/0.74            ( ( l1_pre_topc @ B ) =>
% 0.55/0.74              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.55/0.74                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.55/0.74                  ( v2_tdlat_3 @ A ) ) =>
% 0.55/0.74                ( v2_tdlat_3 @ B ) ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t18_tex_2])).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.55/0.74         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t59_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_pre_topc @
% 0.55/0.74             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.55/0.74           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      (![X11 : $i, X12 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X11 @ 
% 0.55/0.74             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.55/0.74          | (m1_pre_topc @ X11 @ X12)
% 0.55/0.74          | ~ (l1_pre_topc @ X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X0 @ 
% 0.55/0.74             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | (m1_pre_topc @ X0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.74  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X0 @ 
% 0.55/0.74             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.55/0.74          | (m1_pre_topc @ X0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['6', '7'])).
% 0.55/0.74  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['3', '8'])).
% 0.55/0.74  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('11', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.55/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.55/0.74  thf(t35_borsuk_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.74           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (![X27 : $i, X28 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X27 @ X28)
% 0.55/0.74          | (r1_tarski @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 0.55/0.74          | ~ (l1_pre_topc @ X28))),
% 0.55/0.74      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_B)
% 0.55/0.74        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('15', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['13', '14'])).
% 0.55/0.74  thf(d10_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.74  thf('16', plain,
% 0.55/0.74      (![X0 : $i, X2 : $i]:
% 0.55/0.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.55/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.55/0.74        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['15', '16'])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.55/0.74         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((m1_pre_topc @ X0 @ 
% 0.55/0.74           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['2'])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (((m1_pre_topc @ sk_B @ 
% 0.55/0.74         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['18', '19'])).
% 0.55/0.74  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      ((m1_pre_topc @ sk_B @ 
% 0.55/0.74        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['20', '21'])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      (![X11 : $i, X12 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X11 @ 
% 0.55/0.74             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.55/0.74          | (m1_pre_topc @ X11 @ X12)
% 0.55/0.74          | ~ (l1_pre_topc @ X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.55/0.74  thf('24', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.74  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      (![X27 : $i, X28 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X27 @ X28)
% 0.55/0.74          | (r1_tarski @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 0.55/0.74          | ~ (l1_pre_topc @ X28))),
% 0.55/0.74      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.55/0.74  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('30', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['28', '29'])).
% 0.55/0.74  thf('31', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['17', '30'])).
% 0.55/0.74  thf(dt_u1_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( m1_subset_1 @
% 0.55/0.74         ( u1_pre_topc @ A ) @ 
% 0.55/0.74         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      (![X10 : $i]:
% 0.55/0.74         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.55/0.74           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.55/0.74          | ~ (l1_pre_topc @ X10))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.55/0.74         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['31', '32'])).
% 0.55/0.74  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.55/0.74  thf(t78_tops_2, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @
% 0.55/0.74             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.74           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      (![X22 : $i, X23 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X22 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 0.55/0.74          | ~ (v1_tops_2 @ X22 @ X23)
% 0.55/0.74          | (r1_tarski @ X22 @ (u1_pre_topc @ X23))
% 0.55/0.74          | ~ (l1_pre_topc @ X23))),
% 0.55/0.74      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.55/0.74        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.74  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      (((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.55/0.74        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['37', '38'])).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (![X10 : $i]:
% 0.55/0.74         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.55/0.74           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.55/0.74          | ~ (l1_pre_topc @ X10))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.55/0.74  thf(t35_tops_2, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @
% 0.55/0.74             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_pre_topc @ C @ A ) =>
% 0.55/0.74               ( ( v1_tops_2 @ B @ A ) =>
% 0.55/0.74                 ( ![D:$i]:
% 0.55/0.74                   ( ( m1_subset_1 @
% 0.55/0.74                       D @ 
% 0.55/0.74                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.55/0.74                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X18 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.55/0.74          | ~ (v1_tops_2 @ X18 @ X19)
% 0.55/0.74          | ~ (m1_subset_1 @ X20 @ 
% 0.55/0.74               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.55/0.74          | (v1_tops_2 @ X20 @ X21)
% 0.55/0.74          | ((X20) != (X18))
% 0.55/0.74          | ~ (m1_pre_topc @ X21 @ X19)
% 0.55/0.74          | ~ (l1_pre_topc @ X19))),
% 0.55/0.74      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.55/0.74  thf('43', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X19)
% 0.55/0.74          | ~ (m1_pre_topc @ X21 @ X19)
% 0.55/0.74          | (v1_tops_2 @ X18 @ X21)
% 0.55/0.74          | ~ (m1_subset_1 @ X18 @ 
% 0.55/0.74               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.55/0.74          | ~ (v1_tops_2 @ X18 @ X19)
% 0.55/0.74          | ~ (m1_subset_1 @ X18 @ 
% 0.55/0.74               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['42'])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.55/0.74          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ X0)
% 0.55/0.74          | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['41', '43'])).
% 0.55/0.74  thf('45', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_B)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74        | ~ (m1_pre_topc @ sk_A @ sk_B)
% 0.55/0.74        | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)
% 0.55/0.74        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['40', '44'])).
% 0.55/0.74  thf('46', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('48', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.55/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.55/0.74  thf('49', plain,
% 0.55/0.74      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.55/0.74  thf('50', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['17', '30'])).
% 0.55/0.74  thf('51', plain,
% 0.55/0.74      (![X22 : $i, X23 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X22 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 0.55/0.74          | ~ (r1_tarski @ X22 @ (u1_pre_topc @ X23))
% 0.55/0.74          | (v1_tops_2 @ X22 @ X23)
% 0.55/0.74          | ~ (l1_pre_topc @ X23))),
% 0.55/0.74      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.55/0.74  thf('52', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | (v1_tops_2 @ X0 @ sk_B)
% 0.55/0.74          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['50', '51'])).
% 0.55/0.74  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('54', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.74          | (v1_tops_2 @ X0 @ sk_B)
% 0.55/0.74          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.74  thf('55', plain,
% 0.55/0.74      ((~ (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.55/0.74        | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['49', '54'])).
% 0.55/0.74  thf('56', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.55/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.74  thf('57', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.55/0.74      inference('simplify', [status(thm)], ['56'])).
% 0.55/0.74  thf('58', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B)),
% 0.55/0.74      inference('demod', [status(thm)], ['55', '57'])).
% 0.55/0.74  thf('59', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['45', '46', '47', '48', '58'])).
% 0.55/0.74  thf('60', plain, ((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['39', '59'])).
% 0.55/0.74  thf('61', plain,
% 0.55/0.74      (![X0 : $i, X2 : $i]:
% 0.55/0.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.55/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.74  thf('62', plain,
% 0.55/0.74      ((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.55/0.74        | ((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['60', '61'])).
% 0.55/0.74  thf(d2_tdlat_3, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ( v2_tdlat_3 @ A ) <=>
% 0.55/0.74         ( ( u1_pre_topc @ A ) =
% 0.55/0.74           ( k2_tarski @ k1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.55/0.74  thf('63', plain,
% 0.55/0.74      (![X33 : $i]:
% 0.55/0.74         (~ (v2_tdlat_3 @ X33)
% 0.55/0.74          | ((u1_pre_topc @ X33)
% 0.55/0.74              = (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X33)))
% 0.55/0.74          | ~ (l1_pre_topc @ X33))),
% 0.55/0.74      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.55/0.74  thf('64', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['17', '30'])).
% 0.55/0.74  thf('65', plain,
% 0.55/0.74      (![X33 : $i]:
% 0.55/0.74         (((u1_pre_topc @ X33)
% 0.55/0.74            != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ X33)))
% 0.55/0.74          | (v2_tdlat_3 @ X33)
% 0.55/0.74          | ~ (l1_pre_topc @ X33))),
% 0.55/0.74      inference('cnf', [status(esa)], [d2_tdlat_3])).
% 0.55/0.74  thf('66', plain,
% 0.55/0.74      ((((u1_pre_topc @ sk_B)
% 0.55/0.74          != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74        | (v2_tdlat_3 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['64', '65'])).
% 0.55/0.74  thf('67', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('68', plain,
% 0.55/0.74      ((((u1_pre_topc @ sk_B)
% 0.55/0.74          != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.55/0.74        | (v2_tdlat_3 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['66', '67'])).
% 0.55/0.74  thf('69', plain, (~ (v2_tdlat_3 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('70', plain,
% 0.55/0.74      (((u1_pre_topc @ sk_B)
% 0.55/0.74         != (k2_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('clc', [status(thm)], ['68', '69'])).
% 0.55/0.74  thf('71', plain,
% 0.55/0.74      ((((u1_pre_topc @ sk_B) != (u1_pre_topc @ sk_A))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ~ (v2_tdlat_3 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['63', '70'])).
% 0.55/0.74  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('73', plain, ((v2_tdlat_3 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('74', plain, (((u1_pre_topc @ sk_B) != (u1_pre_topc @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.55/0.74  thf('75', plain,
% 0.55/0.74      (~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))),
% 0.55/0.74      inference('simplify_reflect-', [status(thm)], ['62', '74'])).
% 0.55/0.74  thf('76', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.55/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.55/0.74  thf('77', plain,
% 0.55/0.74      (![X10 : $i]:
% 0.55/0.74         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.55/0.74           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.55/0.74          | ~ (l1_pre_topc @ X10))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.55/0.74  thf(t31_tops_2, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_subset_1 @
% 0.55/0.74                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.55/0.74               ( m1_subset_1 @
% 0.55/0.74                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('78', plain,
% 0.55/0.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X15 @ X16)
% 0.55/0.74          | (m1_subset_1 @ X17 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.55/0.74          | ~ (m1_subset_1 @ X17 @ 
% 0.55/0.74               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.55/0.74          | ~ (l1_pre_topc @ X16))),
% 0.55/0.74      inference('cnf', [status(esa)], [t31_tops_2])).
% 0.55/0.74  thf('79', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X1)
% 0.55/0.74          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['77', '78'])).
% 0.55/0.74  thf('80', plain,
% 0.55/0.74      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.55/0.74         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['76', '79'])).
% 0.55/0.74  thf('81', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['17', '30'])).
% 0.55/0.74  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('84', plain,
% 0.55/0.74      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.55/0.74  thf('85', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['17', '30'])).
% 0.55/0.74  thf('86', plain,
% 0.55/0.74      (![X22 : $i, X23 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X22 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 0.55/0.74          | ~ (v1_tops_2 @ X22 @ X23)
% 0.55/0.74          | (r1_tarski @ X22 @ (u1_pre_topc @ X23))
% 0.55/0.74          | ~ (l1_pre_topc @ X23))),
% 0.55/0.74      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.55/0.74  thf('87', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | (r1_tarski @ X0 @ (u1_pre_topc @ sk_B))
% 0.55/0.74          | ~ (v1_tops_2 @ X0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['85', '86'])).
% 0.55/0.74  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('89', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.74          | (r1_tarski @ X0 @ (u1_pre_topc @ sk_B))
% 0.55/0.74          | ~ (v1_tops_2 @ X0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['87', '88'])).
% 0.55/0.74  thf('90', plain,
% 0.55/0.74      ((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.55/0.74        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['84', '89'])).
% 0.55/0.74  thf('91', plain,
% 0.55/0.74      (![X10 : $i]:
% 0.55/0.74         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.55/0.74           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.55/0.74          | ~ (l1_pre_topc @ X10))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.55/0.74  thf('92', plain,
% 0.55/0.74      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.55/0.74  thf('93', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['17', '30'])).
% 0.55/0.74  thf('94', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X19)
% 0.55/0.74          | ~ (m1_pre_topc @ X21 @ X19)
% 0.55/0.74          | (v1_tops_2 @ X18 @ X21)
% 0.55/0.74          | ~ (m1_subset_1 @ X18 @ 
% 0.55/0.74               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.55/0.74          | ~ (v1_tops_2 @ X18 @ X19)
% 0.55/0.74          | ~ (m1_subset_1 @ X18 @ 
% 0.55/0.74               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['42'])).
% 0.55/0.74  thf('95', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ 
% 0.55/0.74               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.55/0.74          | ~ (v1_tops_2 @ X0 @ X1)
% 0.55/0.74          | (v1_tops_2 @ X0 @ sk_B)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 0.55/0.74          | ~ (l1_pre_topc @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['93', '94'])).
% 0.55/0.74  thf('96', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.55/0.74          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.55/0.74          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0)
% 0.55/0.74          | ~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.55/0.74               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['92', '95'])).
% 0.55/0.74  thf('97', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.55/0.74        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.55/0.74        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['91', '96'])).
% 0.55/0.74  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('99', plain,
% 0.55/0.74      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.55/0.74  thf('100', plain,
% 0.55/0.74      (![X22 : $i, X23 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X22 @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 0.55/0.74          | ~ (r1_tarski @ X22 @ (u1_pre_topc @ X23))
% 0.55/0.74          | (v1_tops_2 @ X22 @ X23)
% 0.55/0.74          | ~ (l1_pre_topc @ X23))),
% 0.55/0.74      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.55/0.74  thf('101', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.55/0.74        | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['99', '100'])).
% 0.55/0.74  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('103', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.55/0.74      inference('simplify', [status(thm)], ['56'])).
% 0.55/0.74  thf('104', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.55/0.74  thf('105', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.55/0.74  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('107', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)),
% 0.55/0.74      inference('demod', [status(thm)], ['97', '98', '104', '105', '106'])).
% 0.55/0.74  thf('108', plain,
% 0.55/0.74      ((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['90', '107'])).
% 0.55/0.74  thf('109', plain, ($false), inference('demod', [status(thm)], ['75', '108'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
