%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IzXLflKuNF

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 299 expanded)
%              Number of leaves         :   28 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          : 1394 (4430 expanded)
%              Number of equality atoms :   60 ( 190 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(t106_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k6_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_tmap_1])).

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X3 @ X4 )
      | ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
          <=> ( ( u1_pre_topc @ A )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ( ( u1_pre_topc @ X17 )
        = ( k5_tmap_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k6_tmap_1 @ X11 @ X10 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( k5_tmap_1 @ X11 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf('28',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( u1_pre_topc @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( u1_pre_topc @ X21 ) @ ( k5_tmap_1 @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t99_tmap_1])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k5_tmap_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_tmap_1])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X19 @ X18 ) )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( r1_tarski @ X5 @ ( u1_pre_topc @ X6 ) )
      | ( v1_tops_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('60',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['57','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X19 @ X18 ) )
        = ( k5_tmap_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','75','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('80',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t32_compts_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tops_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
        <=> ( ( v1_tops_2 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_tops_2 @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) ) ) ) )
      | ( v1_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,
    ( ( ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','90'])).

thf('92',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('93',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_tops_2 @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( u1_pre_topc @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,
    ( ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ( ( u1_pre_topc @ sk_A )
        = ( k5_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_pre_topc @ X17 )
       != ( k5_tmap_1 @ X17 @ X16 ) )
      | ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','108'])).

thf('110',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ( v3_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IzXLflKuNF
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 134 iterations in 0.083s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.55  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.22/0.55  thf(t106_tmap_1, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.55             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.55               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.55            ( l1_pre_topc @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55              ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.55                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.55                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (~
% 0.22/0.55       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.22/0.55       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d5_pre_topc, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.55             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.55          | ~ (v3_pre_topc @ X3 @ X4)
% 0.22/0.55          | (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.22/0.55          | ~ (l1_pre_topc @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.22/0.55        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.22/0.55        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.22/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '8'])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t103_tmap_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.22/0.55             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.55          | ~ (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.22/0.55          | ((u1_pre_topc @ X17) = (k5_tmap_1 @ X17 @ X16))
% 0.22/0.55          | ~ (l1_pre_topc @ X17)
% 0.22/0.55          | ~ (v2_pre_topc @ X17)
% 0.22/0.55          | (v2_struct_0 @ X17))),
% 0.22/0.55      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.55  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.22/0.55        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['9', '17'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d9_tmap_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( k6_tmap_1 @ A @ B ) =
% 0.22/0.55             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X10 : $i, X11 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.55          | ((k6_tmap_1 @ X11 @ X10)
% 0.22/0.55              = (g1_pre_topc @ (u1_struct_0 @ X11) @ (k5_tmap_1 @ X11 @ X10)))
% 0.22/0.55          | ~ (l1_pre_topc @ X11)
% 0.22/0.55          | ~ (v2_pre_topc @ X11)
% 0.22/0.55          | (v2_struct_0 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.22/0.55            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.55  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.22/0.55            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.22/0.55  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.22/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.22/0.55          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.22/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['18', '26'])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.22/0.55             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.22/0.55       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.22/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.22/0.55       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t99_tmap_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( r1_tarski @ ( u1_pre_topc @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X20 : $i, X21 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.22/0.55          | (r1_tarski @ (u1_pre_topc @ X21) @ (k5_tmap_1 @ X21 @ X20))
% 0.22/0.55          | ~ (l1_pre_topc @ X21)
% 0.22/0.55          | ~ (v2_pre_topc @ X21)
% 0.22/0.55          | (v2_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [t99_tmap_1])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.55  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.22/0.55  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      ((r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('clc', [status(thm)], ['37', '38'])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_k5_tmap_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.55         ( l1_pre_topc @ A ) & 
% 0.22/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.55       ( m1_subset_1 @
% 0.22/0.55         ( k5_tmap_1 @ A @ B ) @ 
% 0.22/0.55         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i]:
% 0.22/0.55         (~ (l1_pre_topc @ X12)
% 0.22/0.55          | ~ (v2_pre_topc @ X12)
% 0.22/0.55          | (v2_struct_0 @ X12)
% 0.22/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.55          | (m1_subset_1 @ (k5_tmap_1 @ X12 @ X13) @ 
% 0.22/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k5_tmap_1])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.55         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.55        | (v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.55  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.55         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.55        | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.55  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t104_tmap_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.55             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (![X18 : $i, X19 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.55          | ((u1_struct_0 @ (k6_tmap_1 @ X19 @ X18)) = (u1_struct_0 @ X19))
% 0.22/0.55          | ~ (l1_pre_topc @ X19)
% 0.22/0.55          | ~ (v2_pre_topc @ X19)
% 0.22/0.55          | (v2_struct_0 @ X19))),
% 0.22/0.55      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.22/0.55  thf('50', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.55  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.22/0.55  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.22/0.55  thf(t78_tops_2, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @
% 0.22/0.55             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.55           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X5 @ 
% 0.22/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))
% 0.22/0.55          | ~ (r1_tarski @ X5 @ (u1_pre_topc @ X6))
% 0.22/0.55          | (v1_tops_2 @ X5 @ X6)
% 0.22/0.55          | ~ (l1_pre_topc @ X6))),
% 0.22/0.55      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X0 @ 
% 0.22/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.55          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55          | (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_k6_tmap_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.55         ( l1_pre_topc @ A ) & 
% 0.22/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.55       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.22/0.55         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.22/0.55         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      (![X14 : $i, X15 : $i]:
% 0.22/0.55         (~ (l1_pre_topc @ X14)
% 0.22/0.55          | ~ (v2_pre_topc @ X14)
% 0.22/0.55          | (v2_struct_0 @ X14)
% 0.22/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.55          | (l1_pre_topc @ (k6_tmap_1 @ X14 @ X15)))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.22/0.55  thf('60', plain,
% 0.22/0.55      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55        | (v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('63', plain,
% 0.22/0.55      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.22/0.55  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('65', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('clc', [status(thm)], ['63', '64'])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X0 @ 
% 0.22/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.55          | (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['57', '65'])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      ((~ (r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.55           (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.55        | (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['47', '66'])).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      (![X18 : $i, X19 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.55          | ((u1_pre_topc @ (k6_tmap_1 @ X19 @ X18)) = (k5_tmap_1 @ X19 @ X18))
% 0.22/0.55          | ~ (l1_pre_topc @ X19)
% 0.22/0.55          | ~ (v2_pre_topc @ X19)
% 0.22/0.55          | (v2_struct_0 @ X19))),
% 0.22/0.55      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.22/0.55  thf('70', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.55  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.22/0.55  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('75', plain,
% 0.22/0.55      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('clc', [status(thm)], ['73', '74'])).
% 0.22/0.55  thf(d10_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.55  thf('77', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.55      inference('simplify', [status(thm)], ['76'])).
% 0.22/0.55  thf('78', plain,
% 0.22/0.55      ((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['67', '75', '77'])).
% 0.22/0.55  thf('79', plain,
% 0.22/0.55      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf('80', plain,
% 0.22/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf(t32_compts_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( v1_tops_2 @ B @ A ) & 
% 0.22/0.55             ( m1_subset_1 @
% 0.22/0.55               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.22/0.55           ( ( v1_tops_2 @
% 0.22/0.55               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.22/0.55             ( m1_subset_1 @
% 0.22/0.55               B @ 
% 0.22/0.55               ( k1_zfmisc_1 @
% 0.22/0.55                 ( k1_zfmisc_1 @
% 0.22/0.55                   ( u1_struct_0 @
% 0.22/0.55                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('81', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i]:
% 0.22/0.55         (~ (v1_tops_2 @ X7 @ 
% 0.22/0.55             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.22/0.55          | ~ (m1_subset_1 @ X7 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k1_zfmisc_1 @ 
% 0.22/0.55                 (u1_struct_0 @ 
% 0.22/0.55                  (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8))))))
% 0.22/0.55          | (v1_tops_2 @ X7 @ X8)
% 0.22/0.55          | ~ (l1_pre_topc @ X8)
% 0.22/0.55          | ~ (v2_pre_topc @ X8)
% 0.22/0.55          | (v2_struct_0 @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.22/0.55  thf('82', plain,
% 0.22/0.55      ((![X0 : $i]:
% 0.22/0.55          (~ (m1_subset_1 @ X0 @ 
% 0.22/0.55              (k1_zfmisc_1 @ 
% 0.22/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.22/0.55           | (v2_struct_0 @ sk_A)
% 0.22/0.55           | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55           | ~ (l1_pre_topc @ sk_A)
% 0.22/0.55           | (v1_tops_2 @ X0 @ sk_A)
% 0.22/0.55           | ~ (v1_tops_2 @ X0 @ 
% 0.22/0.55                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['80', '81'])).
% 0.22/0.55  thf('83', plain,
% 0.22/0.55      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.22/0.55  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('86', plain,
% 0.22/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('87', plain,
% 0.22/0.55      ((![X0 : $i]:
% 0.22/0.55          (~ (m1_subset_1 @ X0 @ 
% 0.22/0.55              (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.55           | (v2_struct_0 @ sk_A)
% 0.22/0.55           | (v1_tops_2 @ X0 @ sk_A)
% 0.22/0.55           | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.22/0.55  thf('88', plain,
% 0.22/0.55      (((~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55         | (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.55         | (v2_struct_0 @ sk_A)))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['79', '87'])).
% 0.22/0.55  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('90', plain,
% 0.22/0.55      ((((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.55         | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('clc', [status(thm)], ['88', '89'])).
% 0.22/0.55  thf('91', plain,
% 0.22/0.55      (((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['78', '90'])).
% 0.22/0.55  thf('92', plain,
% 0.22/0.55      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf('93', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X5 @ 
% 0.22/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))
% 0.22/0.55          | ~ (v1_tops_2 @ X5 @ X6)
% 0.22/0.55          | (r1_tarski @ X5 @ (u1_pre_topc @ X6))
% 0.22/0.55          | ~ (l1_pre_topc @ X6))),
% 0.22/0.55      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.22/0.55  thf('94', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | (r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.22/0.55        | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['92', '93'])).
% 0.22/0.55  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('96', plain,
% 0.22/0.55      (((r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.22/0.55        | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.22/0.55  thf('97', plain,
% 0.22/0.55      (((r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['91', '96'])).
% 0.22/0.55  thf('98', plain,
% 0.22/0.55      (![X0 : $i, X2 : $i]:
% 0.22/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.55  thf('99', plain,
% 0.22/0.55      (((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55         | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['97', '98'])).
% 0.22/0.55  thf('100', plain,
% 0.22/0.55      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['39', '99'])).
% 0.22/0.55  thf('101', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('102', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.55          | ((u1_pre_topc @ X17) != (k5_tmap_1 @ X17 @ X16))
% 0.22/0.55          | (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.22/0.55          | ~ (l1_pre_topc @ X17)
% 0.22/0.55          | ~ (v2_pre_topc @ X17)
% 0.22/0.55          | (v2_struct_0 @ X17))),
% 0.22/0.55      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.22/0.55  thf('103', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.22/0.55        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['101', '102'])).
% 0.22/0.55  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('106', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.22/0.55        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.22/0.55  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('108', plain,
% 0.22/0.55      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.22/0.55        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['106', '107'])).
% 0.22/0.55  thf('109', plain,
% 0.22/0.55      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.22/0.55         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['100', '108'])).
% 0.22/0.55  thf('110', plain,
% 0.22/0.55      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('simplify', [status(thm)], ['109'])).
% 0.22/0.55  thf('111', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('112', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.55          | ~ (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.22/0.55          | (v3_pre_topc @ X3 @ X4)
% 0.22/0.55          | ~ (l1_pre_topc @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.22/0.55  thf('113', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | (v3_pre_topc @ sk_B @ sk_A)
% 0.22/0.55        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['111', '112'])).
% 0.22/0.55  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('115', plain,
% 0.22/0.55      (((v3_pre_topc @ sk_B @ sk_A)
% 0.22/0.55        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['113', '114'])).
% 0.22/0.55  thf('116', plain,
% 0.22/0.55      (((v3_pre_topc @ sk_B @ sk_A))
% 0.22/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['110', '115'])).
% 0.22/0.55  thf('117', plain,
% 0.22/0.55      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('118', plain,
% 0.22/0.55      (~
% 0.22/0.55       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.55          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.22/0.55       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['116', '117'])).
% 0.22/0.55  thf('119', plain, ($false),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '118'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
