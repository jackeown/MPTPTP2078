%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uDq2WYJdQ2

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:45 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 327 expanded)
%              Number of leaves         :   47 ( 119 expanded)
%              Depth                    :   26
%              Number of atoms          : 1655 (4375 expanded)
%              Number of equality atoms :   85 ( 214 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

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
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ( r2_hidden @ X28 @ ( u1_pre_topc @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r2_hidden @ X32 @ ( u1_pre_topc @ X33 ) )
      | ( ( u1_pre_topc @ X33 )
        = ( k5_tmap_1 @ X33 @ X32 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
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
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X35 @ X34 ) )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('28',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('30',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('31',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('39',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['28','36','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X35 @ X34 ) )
        = ( k5_tmap_1 @ X35 @ X34 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( k5_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['45','53'])).

thf('55',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','54'])).

thf('56',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_2 )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      & ( v3_pre_topc @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('60',plain,(
    ! [X25: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ( r2_hidden @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('61',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('63',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r2_hidden @ X32 @ ( u1_pre_topc @ X33 ) )
      | ( ( u1_pre_topc @ X33 )
        = ( k5_tmap_1 @ X33 @ X32 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('70',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('71',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X35 @ X34 ) )
        = ( k5_tmap_1 @ X35 @ X34 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('74',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('77',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('80',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X35 @ X34 ) )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['75','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['68','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('99',plain,
    ( ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( k5_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
        = ( u1_pre_topc @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['67','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
        = ( u1_pre_topc @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B_2 )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( u1_pre_topc @ X33 )
       != ( k5_tmap_1 @ X33 @ X32 ) )
      | ( r2_hidden @ X32 @ ( u1_pre_topc @ X33 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['111','119'])).

thf('121',plain,
    ( ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r2_hidden @ X28 @ ( u1_pre_topc @ X29 ) )
      | ( v3_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['121','126'])).

thf('128',plain,
    ( ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('129',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uDq2WYJdQ2
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.68/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.85  % Solved by: fo/fo7.sh
% 0.68/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.85  % done 647 iterations in 0.398s
% 0.68/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.85  % SZS output start Refutation
% 0.68/0.85  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.68/0.85  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.68/0.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.85  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.68/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.85  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.68/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.68/0.85  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.68/0.85  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.68/0.85  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.68/0.85  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.68/0.85  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.68/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.85  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.68/0.85  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.68/0.85  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.68/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.85  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.68/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.68/0.85  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.68/0.85  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.68/0.85  thf(t106_tmap_1, conjecture,
% 0.68/0.85    (![A:$i]:
% 0.68/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.85       ( ![B:$i]:
% 0.68/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.85           ( ( v3_pre_topc @ B @ A ) <=>
% 0.68/0.85             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.68/0.85               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.68/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.85    (~( ![A:$i]:
% 0.68/0.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.68/0.85            ( l1_pre_topc @ A ) ) =>
% 0.68/0.85          ( ![B:$i]:
% 0.68/0.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.85              ( ( v3_pre_topc @ B @ A ) <=>
% 0.68/0.85                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.68/0.85                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.68/0.85    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.68/0.85  thf('0', plain,
% 0.68/0.85      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85          != (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85        | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('1', plain,
% 0.68/0.85      (~
% 0.68/0.85       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85          = (k6_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.68/0.85       ~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.68/0.85      inference('split', [status(esa)], ['0'])).
% 0.68/0.85  thf('2', plain,
% 0.68/0.85      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85          = (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85        | (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('3', plain,
% 0.68/0.85      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.68/0.85      inference('split', [status(esa)], ['2'])).
% 0.68/0.85  thf('4', plain,
% 0.68/0.85      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf(d5_pre_topc, axiom,
% 0.68/0.85    (![A:$i]:
% 0.68/0.85     ( ( l1_pre_topc @ A ) =>
% 0.68/0.85       ( ![B:$i]:
% 0.68/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.85           ( ( v3_pre_topc @ B @ A ) <=>
% 0.68/0.85             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.68/0.85  thf('5', plain,
% 0.68/0.85      (![X28 : $i, X29 : $i]:
% 0.68/0.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.68/0.85          | ~ (v3_pre_topc @ X28 @ X29)
% 0.68/0.85          | (r2_hidden @ X28 @ (u1_pre_topc @ X29))
% 0.68/0.85          | ~ (l1_pre_topc @ X29))),
% 0.68/0.85      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.68/0.85  thf('6', plain,
% 0.68/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.85        | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.68/0.85        | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.68/0.85      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.85  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('8', plain,
% 0.68/0.85      (((r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.68/0.85        | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.68/0.85      inference('demod', [status(thm)], ['6', '7'])).
% 0.68/0.85  thf('9', plain,
% 0.68/0.85      (((r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))
% 0.68/0.85         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['3', '8'])).
% 0.68/0.85  thf('10', plain,
% 0.68/0.85      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf(t103_tmap_1, axiom,
% 0.68/0.85    (![A:$i]:
% 0.68/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.85       ( ![B:$i]:
% 0.68/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.85           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.68/0.85             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.68/0.85  thf('11', plain,
% 0.68/0.85      (![X32 : $i, X33 : $i]:
% 0.68/0.85         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.68/0.85          | ~ (r2_hidden @ X32 @ (u1_pre_topc @ X33))
% 0.68/0.85          | ((u1_pre_topc @ X33) = (k5_tmap_1 @ X33 @ X32))
% 0.68/0.85          | ~ (l1_pre_topc @ X33)
% 0.68/0.85          | ~ (v2_pre_topc @ X33)
% 0.68/0.85          | (v2_struct_0 @ X33))),
% 0.68/0.85      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.68/0.85  thf('12', plain,
% 0.68/0.85      (((v2_struct_0 @ sk_A)
% 0.68/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.85        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.85        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85        | ~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['10', '11'])).
% 0.68/0.85  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('15', plain,
% 0.68/0.85      (((v2_struct_0 @ sk_A)
% 0.68/0.85        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85        | ~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.68/0.85      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.68/0.85  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('17', plain,
% 0.68/0.85      ((~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.68/0.85        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.68/0.85      inference('clc', [status(thm)], ['15', '16'])).
% 0.68/0.85  thf('18', plain,
% 0.68/0.85      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_2)))
% 0.68/0.85         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['9', '17'])).
% 0.68/0.85  thf('19', plain,
% 0.68/0.85      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf(t104_tmap_1, axiom,
% 0.68/0.85    (![A:$i]:
% 0.68/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.85       ( ![B:$i]:
% 0.68/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.85           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.68/0.85             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.68/0.85  thf('20', plain,
% 0.68/0.85      (![X34 : $i, X35 : $i]:
% 0.68/0.85         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.68/0.85          | ((u1_struct_0 @ (k6_tmap_1 @ X35 @ X34)) = (u1_struct_0 @ X35))
% 0.68/0.85          | ~ (l1_pre_topc @ X35)
% 0.68/0.85          | ~ (v2_pre_topc @ X35)
% 0.68/0.85          | (v2_struct_0 @ X35))),
% 0.68/0.85      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.68/0.85  thf('21', plain,
% 0.68/0.85      (((v2_struct_0 @ sk_A)
% 0.68/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.85        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.85        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['19', '20'])).
% 0.68/0.85  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('24', plain,
% 0.68/0.85      (((v2_struct_0 @ sk_A)
% 0.68/0.85        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.68/0.85  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('26', plain,
% 0.68/0.85      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))),
% 0.68/0.85      inference('clc', [status(thm)], ['24', '25'])).
% 0.68/0.85  thf(abstractness_v1_pre_topc, axiom,
% 0.68/0.85    (![A:$i]:
% 0.68/0.85     ( ( l1_pre_topc @ A ) =>
% 0.68/0.85       ( ( v1_pre_topc @ A ) =>
% 0.68/0.85         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.68/0.85  thf('27', plain,
% 0.68/0.85      (![X2 : $i]:
% 0.68/0.85         (~ (v1_pre_topc @ X2)
% 0.68/0.85          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.68/0.85          | ~ (l1_pre_topc @ X2))),
% 0.68/0.85      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.68/0.85  thf('28', plain,
% 0.68/0.85      ((((k6_tmap_1 @ sk_A @ sk_B_2)
% 0.68/0.85          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.85             (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))))
% 0.68/0.85        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2)))),
% 0.68/0.85      inference('sup+', [status(thm)], ['26', '27'])).
% 0.68/0.85  thf('29', plain,
% 0.68/0.85      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf(dt_k6_tmap_1, axiom,
% 0.68/0.85    (![A:$i,B:$i]:
% 0.68/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.68/0.85         ( l1_pre_topc @ A ) & 
% 0.68/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.85       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.68/0.85         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.68/0.85         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.68/0.85  thf('30', plain,
% 0.68/0.85      (![X30 : $i, X31 : $i]:
% 0.68/0.85         (~ (l1_pre_topc @ X30)
% 0.68/0.85          | ~ (v2_pre_topc @ X30)
% 0.68/0.85          | (v2_struct_0 @ X30)
% 0.68/0.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.68/0.85          | (l1_pre_topc @ (k6_tmap_1 @ X30 @ X31)))),
% 0.68/0.85      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.68/0.85  thf('31', plain,
% 0.68/0.85      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85        | (v2_struct_0 @ sk_A)
% 0.68/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.68/0.85  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('34', plain,
% 0.68/0.85      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.68/0.85      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.68/0.85  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('36', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))),
% 0.68/0.85      inference('clc', [status(thm)], ['34', '35'])).
% 0.68/0.85  thf('37', plain,
% 0.68/0.85      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('38', plain,
% 0.68/0.85      (![X30 : $i, X31 : $i]:
% 0.68/0.85         (~ (l1_pre_topc @ X30)
% 0.68/0.85          | ~ (v2_pre_topc @ X30)
% 0.68/0.85          | (v2_struct_0 @ X30)
% 0.68/0.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.68/0.85          | (v1_pre_topc @ (k6_tmap_1 @ X30 @ X31)))),
% 0.68/0.85      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.68/0.85  thf('39', plain,
% 0.68/0.85      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85        | (v2_struct_0 @ sk_A)
% 0.68/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.85      inference('sup-', [status(thm)], ['37', '38'])).
% 0.68/0.85  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('42', plain,
% 0.68/0.85      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.68/0.85      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.68/0.85  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('44', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))),
% 0.68/0.85      inference('clc', [status(thm)], ['42', '43'])).
% 0.68/0.85  thf('45', plain,
% 0.68/0.85      (((k6_tmap_1 @ sk_A @ sk_B_2)
% 0.68/0.85         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.85            (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('demod', [status(thm)], ['28', '36', '44'])).
% 0.68/0.85  thf('46', plain,
% 0.68/0.85      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('47', plain,
% 0.68/0.85      (![X34 : $i, X35 : $i]:
% 0.68/0.85         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.68/0.85          | ((u1_pre_topc @ (k6_tmap_1 @ X35 @ X34)) = (k5_tmap_1 @ X35 @ X34))
% 0.68/0.85          | ~ (l1_pre_topc @ X35)
% 0.68/0.85          | ~ (v2_pre_topc @ X35)
% 0.68/0.85          | (v2_struct_0 @ X35))),
% 0.68/0.85      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.68/0.85  thf('48', plain,
% 0.68/0.85      (((v2_struct_0 @ sk_A)
% 0.68/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.85        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.85        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85            = (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['46', '47'])).
% 0.68/0.85  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('51', plain,
% 0.68/0.85      (((v2_struct_0 @ sk_A)
% 0.68/0.85        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85            = (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.68/0.85      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.68/0.85  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('53', plain,
% 0.68/0.85      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85         = (k5_tmap_1 @ sk_A @ sk_B_2))),
% 0.68/0.85      inference('clc', [status(thm)], ['51', '52'])).
% 0.68/0.85  thf('54', plain,
% 0.68/0.85      (((k6_tmap_1 @ sk_A @ sk_B_2)
% 0.68/0.85         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.68/0.85      inference('demod', [status(thm)], ['45', '53'])).
% 0.68/0.85  thf('55', plain,
% 0.68/0.85      ((((k6_tmap_1 @ sk_A @ sk_B_2)
% 0.68/0.85          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.68/0.85         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.68/0.85      inference('sup+', [status(thm)], ['18', '54'])).
% 0.68/0.85  thf('56', plain,
% 0.68/0.85      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85          != (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.68/0.85         <= (~
% 0.68/0.85             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('split', [status(esa)], ['0'])).
% 0.68/0.85  thf('57', plain,
% 0.68/0.85      ((((k6_tmap_1 @ sk_A @ sk_B_2) != (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.68/0.85         <= (~
% 0.68/0.85             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))) & 
% 0.68/0.85             ((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['55', '56'])).
% 0.68/0.85  thf('58', plain,
% 0.68/0.85      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85          = (k6_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.68/0.85       ~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.68/0.85      inference('simplify', [status(thm)], ['57'])).
% 0.68/0.85  thf('59', plain,
% 0.68/0.85      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85          = (k6_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.68/0.85       ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.68/0.85      inference('split', [status(esa)], ['2'])).
% 0.68/0.85  thf(d1_pre_topc, axiom,
% 0.68/0.85    (![A:$i]:
% 0.68/0.85     ( ( l1_pre_topc @ A ) =>
% 0.68/0.85       ( ( v2_pre_topc @ A ) <=>
% 0.68/0.85         ( ( ![B:$i]:
% 0.68/0.85             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.85               ( ![C:$i]:
% 0.68/0.85                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.85                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.68/0.85                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.68/0.85                     ( r2_hidden @
% 0.68/0.85                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.68/0.85                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.68/0.85           ( ![B:$i]:
% 0.68/0.85             ( ( m1_subset_1 @
% 0.68/0.85                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.85               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.68/0.85                 ( r2_hidden @
% 0.68/0.85                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.68/0.85                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.68/0.85           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.68/0.85  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.68/0.85  thf(zf_stmt_2, axiom,
% 0.68/0.85    (![B:$i,A:$i]:
% 0.68/0.85     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.68/0.85       ( ( m1_subset_1 @
% 0.68/0.85           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.85         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.68/0.85  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.68/0.85  thf(zf_stmt_4, axiom,
% 0.68/0.85    (![B:$i,A:$i]:
% 0.68/0.85     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.68/0.85       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.68/0.85         ( r2_hidden @
% 0.68/0.85           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.68/0.85  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.68/0.85  thf(zf_stmt_6, axiom,
% 0.68/0.85    (![B:$i,A:$i]:
% 0.68/0.85     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.68/0.85       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.85         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.68/0.85  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.68/0.85  thf(zf_stmt_8, axiom,
% 0.68/0.85    (![C:$i,B:$i,A:$i]:
% 0.68/0.85     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.68/0.85       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.85         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.68/0.85  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.68/0.85  thf(zf_stmt_10, axiom,
% 0.68/0.85    (![C:$i,B:$i,A:$i]:
% 0.68/0.85     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.68/0.85       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.68/0.85         ( r2_hidden @
% 0.68/0.85           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.68/0.85  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.68/0.85  thf(zf_stmt_12, axiom,
% 0.68/0.85    (![C:$i,B:$i,A:$i]:
% 0.68/0.85     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.68/0.85       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.68/0.85         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.68/0.85  thf(zf_stmt_13, axiom,
% 0.68/0.85    (![A:$i]:
% 0.68/0.85     ( ( l1_pre_topc @ A ) =>
% 0.68/0.85       ( ( v2_pre_topc @ A ) <=>
% 0.68/0.85         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.68/0.85           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.68/0.85           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.68/0.85  thf('60', plain,
% 0.68/0.85      (![X25 : $i]:
% 0.68/0.85         (~ (v2_pre_topc @ X25)
% 0.68/0.85          | (r2_hidden @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25))
% 0.68/0.85          | ~ (l1_pre_topc @ X25))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.68/0.85  thf(dt_k2_subset_1, axiom,
% 0.68/0.85    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.68/0.85  thf('61', plain,
% 0.68/0.85      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.68/0.85      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.68/0.85  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.68/0.85  thf('62', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.68/0.85      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.68/0.85  thf('63', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.68/0.85      inference('demod', [status(thm)], ['61', '62'])).
% 0.68/0.85  thf('64', plain,
% 0.68/0.85      (![X32 : $i, X33 : $i]:
% 0.68/0.85         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.68/0.85          | ~ (r2_hidden @ X32 @ (u1_pre_topc @ X33))
% 0.68/0.85          | ((u1_pre_topc @ X33) = (k5_tmap_1 @ X33 @ X32))
% 0.68/0.85          | ~ (l1_pre_topc @ X33)
% 0.68/0.85          | ~ (v2_pre_topc @ X33)
% 0.68/0.85          | (v2_struct_0 @ X33))),
% 0.68/0.85      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.68/0.85  thf('65', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['63', '64'])).
% 0.68/0.85  thf('66', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         (~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | (v2_struct_0 @ X0))),
% 0.68/0.85      inference('sup-', [status(thm)], ['60', '65'])).
% 0.68/0.85  thf('67', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((v2_struct_0 @ X0)
% 0.68/0.85          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0))),
% 0.68/0.85      inference('simplify', [status(thm)], ['66'])).
% 0.68/0.85  thf('68', plain,
% 0.68/0.85      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85          = (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('split', [status(esa)], ['2'])).
% 0.68/0.85  thf('69', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((v2_struct_0 @ X0)
% 0.68/0.85          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0))),
% 0.68/0.85      inference('simplify', [status(thm)], ['66'])).
% 0.68/0.85  thf('70', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.68/0.85      inference('demod', [status(thm)], ['61', '62'])).
% 0.68/0.85  thf('71', plain,
% 0.68/0.85      (![X34 : $i, X35 : $i]:
% 0.68/0.85         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.68/0.85          | ((u1_pre_topc @ (k6_tmap_1 @ X35 @ X34)) = (k5_tmap_1 @ X35 @ X34))
% 0.68/0.85          | ~ (l1_pre_topc @ X35)
% 0.68/0.85          | ~ (v2_pre_topc @ X35)
% 0.68/0.85          | (v2_struct_0 @ X35))),
% 0.68/0.85      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.68/0.85  thf('72', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.68/0.85      inference('sup-', [status(thm)], ['70', '71'])).
% 0.68/0.85  thf('73', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.68/0.85      inference('demod', [status(thm)], ['61', '62'])).
% 0.68/0.85  thf('74', plain,
% 0.68/0.85      (![X30 : $i, X31 : $i]:
% 0.68/0.85         (~ (l1_pre_topc @ X30)
% 0.68/0.85          | ~ (v2_pre_topc @ X30)
% 0.68/0.85          | (v2_struct_0 @ X30)
% 0.68/0.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.68/0.85          | (v1_pre_topc @ (k6_tmap_1 @ X30 @ X31)))),
% 0.68/0.85      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.68/0.85  thf('75', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0))),
% 0.68/0.85      inference('sup-', [status(thm)], ['73', '74'])).
% 0.68/0.85  thf('76', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.68/0.85      inference('demod', [status(thm)], ['61', '62'])).
% 0.68/0.85  thf('77', plain,
% 0.68/0.85      (![X30 : $i, X31 : $i]:
% 0.68/0.85         (~ (l1_pre_topc @ X30)
% 0.68/0.85          | ~ (v2_pre_topc @ X30)
% 0.68/0.85          | (v2_struct_0 @ X30)
% 0.68/0.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.68/0.85          | (l1_pre_topc @ (k6_tmap_1 @ X30 @ X31)))),
% 0.68/0.85      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.68/0.85  thf('78', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((l1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0))),
% 0.68/0.85      inference('sup-', [status(thm)], ['76', '77'])).
% 0.68/0.85  thf('79', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.68/0.85      inference('demod', [status(thm)], ['61', '62'])).
% 0.68/0.85  thf('80', plain,
% 0.68/0.85      (![X34 : $i, X35 : $i]:
% 0.68/0.85         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.68/0.85          | ((u1_struct_0 @ (k6_tmap_1 @ X35 @ X34)) = (u1_struct_0 @ X35))
% 0.68/0.85          | ~ (l1_pre_topc @ X35)
% 0.68/0.85          | ~ (v2_pre_topc @ X35)
% 0.68/0.85          | (v2_struct_0 @ X35))),
% 0.68/0.85      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.68/0.85  thf('81', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ((u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85              = (u1_struct_0 @ X0)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['79', '80'])).
% 0.68/0.85  thf('82', plain,
% 0.68/0.85      (![X2 : $i]:
% 0.68/0.85         (~ (v1_pre_topc @ X2)
% 0.68/0.85          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.68/0.85          | ~ (l1_pre_topc @ X2))),
% 0.68/0.85      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.68/0.85  thf('83', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.68/0.85            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.68/0.85               (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.68/0.85      inference('sup+', [status(thm)], ['81', '82'])).
% 0.68/0.85  thf('84', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         (~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.68/0.85              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.68/0.85                 (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))),
% 0.68/0.85      inference('sup-', [status(thm)], ['78', '83'])).
% 0.68/0.85  thf('85', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.68/0.85            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.68/0.85               (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))
% 0.68/0.85          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0))),
% 0.68/0.85      inference('simplify', [status(thm)], ['84'])).
% 0.68/0.85  thf('86', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         (~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.68/0.85              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.68/0.85                 (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))),
% 0.68/0.85      inference('sup-', [status(thm)], ['75', '85'])).
% 0.68/0.85  thf('87', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.68/0.85            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.68/0.85               (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0))),
% 0.68/0.85      inference('simplify', [status(thm)], ['86'])).
% 0.68/0.85  thf('88', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.68/0.85            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.68/0.85               (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | (v2_struct_0 @ X0))),
% 0.68/0.85      inference('sup+', [status(thm)], ['72', '87'])).
% 0.68/0.85  thf('89', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.68/0.85              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.68/0.85                 (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))),
% 0.68/0.85      inference('simplify', [status(thm)], ['88'])).
% 0.68/0.85  thf('90', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.68/0.85            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | (v2_struct_0 @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | (v2_struct_0 @ X0))),
% 0.68/0.85      inference('sup+', [status(thm)], ['69', '89'])).
% 0.68/0.85  thf('91', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.68/0.85              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.68/0.85      inference('simplify', [status(thm)], ['90'])).
% 0.68/0.85  thf('92', plain,
% 0.68/0.85      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.68/0.85           = (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85         | ~ (l1_pre_topc @ sk_A)
% 0.68/0.85         | ~ (v2_pre_topc @ sk_A)
% 0.68/0.85         | (v2_struct_0 @ sk_A)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('sup+', [status(thm)], ['68', '91'])).
% 0.68/0.85  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('95', plain,
% 0.68/0.85      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.68/0.85           = (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85         | (v2_struct_0 @ sk_A)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.68/0.85  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('97', plain,
% 0.68/0.85      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.68/0.85          = (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('clc', [status(thm)], ['95', '96'])).
% 0.68/0.85  thf('98', plain,
% 0.68/0.85      (![X0 : $i]:
% 0.68/0.85         ((v2_struct_0 @ X0)
% 0.68/0.85          | ~ (v2_pre_topc @ X0)
% 0.68/0.85          | ~ (l1_pre_topc @ X0)
% 0.68/0.85          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.68/0.85              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.68/0.85      inference('sup-', [status(thm)], ['70', '71'])).
% 0.68/0.85  thf('99', plain,
% 0.68/0.85      (((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85           = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.68/0.85         | ~ (l1_pre_topc @ sk_A)
% 0.68/0.85         | ~ (v2_pre_topc @ sk_A)
% 0.68/0.85         | (v2_struct_0 @ sk_A)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('sup+', [status(thm)], ['97', '98'])).
% 0.68/0.85  thf('100', plain,
% 0.68/0.85      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85         = (k5_tmap_1 @ sk_A @ sk_B_2))),
% 0.68/0.85      inference('clc', [status(thm)], ['51', '52'])).
% 0.68/0.85  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('103', plain,
% 0.68/0.85      (((((k5_tmap_1 @ sk_A @ sk_B_2)
% 0.68/0.85           = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.68/0.85         | (v2_struct_0 @ sk_A)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.68/0.85  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('105', plain,
% 0.68/0.85      ((((k5_tmap_1 @ sk_A @ sk_B_2)
% 0.68/0.85          = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('clc', [status(thm)], ['103', '104'])).
% 0.68/0.85  thf('106', plain,
% 0.68/0.85      (((((k5_tmap_1 @ sk_A @ sk_B_2) = (u1_pre_topc @ sk_A))
% 0.68/0.85         | ~ (l1_pre_topc @ sk_A)
% 0.68/0.85         | ~ (v2_pre_topc @ sk_A)
% 0.68/0.85         | (v2_struct_0 @ sk_A)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('sup+', [status(thm)], ['67', '105'])).
% 0.68/0.85  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('109', plain,
% 0.68/0.85      (((((k5_tmap_1 @ sk_A @ sk_B_2) = (u1_pre_topc @ sk_A))
% 0.68/0.85         | (v2_struct_0 @ sk_A)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.68/0.85  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('111', plain,
% 0.68/0.85      ((((k5_tmap_1 @ sk_A @ sk_B_2) = (u1_pre_topc @ sk_A)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('clc', [status(thm)], ['109', '110'])).
% 0.68/0.85  thf('112', plain,
% 0.68/0.85      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('113', plain,
% 0.68/0.85      (![X32 : $i, X33 : $i]:
% 0.68/0.85         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.68/0.85          | ((u1_pre_topc @ X33) != (k5_tmap_1 @ X33 @ X32))
% 0.68/0.85          | (r2_hidden @ X32 @ (u1_pre_topc @ X33))
% 0.68/0.85          | ~ (l1_pre_topc @ X33)
% 0.68/0.85          | ~ (v2_pre_topc @ X33)
% 0.68/0.85          | (v2_struct_0 @ X33))),
% 0.68/0.85      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.68/0.85  thf('114', plain,
% 0.68/0.85      (((v2_struct_0 @ sk_A)
% 0.68/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.85        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.85        | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.68/0.85        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['112', '113'])).
% 0.68/0.85  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('117', plain,
% 0.68/0.85      (((v2_struct_0 @ sk_A)
% 0.68/0.85        | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.68/0.85        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_2)))),
% 0.68/0.85      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.68/0.85  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('119', plain,
% 0.68/0.85      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_2))
% 0.68/0.85        | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.68/0.85      inference('clc', [status(thm)], ['117', '118'])).
% 0.68/0.85  thf('120', plain,
% 0.68/0.85      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.68/0.85         | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('sup-', [status(thm)], ['111', '119'])).
% 0.68/0.85  thf('121', plain,
% 0.68/0.85      (((r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('simplify', [status(thm)], ['120'])).
% 0.68/0.85  thf('122', plain,
% 0.68/0.85      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('123', plain,
% 0.68/0.85      (![X28 : $i, X29 : $i]:
% 0.68/0.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.68/0.85          | ~ (r2_hidden @ X28 @ (u1_pre_topc @ X29))
% 0.68/0.85          | (v3_pre_topc @ X28 @ X29)
% 0.68/0.85          | ~ (l1_pre_topc @ X29))),
% 0.68/0.85      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.68/0.85  thf('124', plain,
% 0.68/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.68/0.85        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.68/0.85        | ~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.68/0.85      inference('sup-', [status(thm)], ['122', '123'])).
% 0.68/0.85  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf('126', plain,
% 0.68/0.85      (((v3_pre_topc @ sk_B_2 @ sk_A)
% 0.68/0.85        | ~ (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.68/0.85      inference('demod', [status(thm)], ['124', '125'])).
% 0.68/0.85  thf('127', plain,
% 0.68/0.85      (((v3_pre_topc @ sk_B_2 @ sk_A))
% 0.68/0.85         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85                = (k6_tmap_1 @ sk_A @ sk_B_2))))),
% 0.68/0.85      inference('sup-', [status(thm)], ['121', '126'])).
% 0.68/0.85  thf('128', plain,
% 0.68/0.85      ((~ (v3_pre_topc @ sk_B_2 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.68/0.85      inference('split', [status(esa)], ['0'])).
% 0.68/0.85  thf('129', plain,
% 0.68/0.85      (~
% 0.68/0.85       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.68/0.85          = (k6_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.68/0.85       ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.68/0.85      inference('sup-', [status(thm)], ['127', '128'])).
% 0.68/0.85  thf('130', plain, ($false),
% 0.68/0.85      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '129'])).
% 0.68/0.85  
% 0.68/0.85  % SZS output end Refutation
% 0.68/0.85  
% 0.68/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
