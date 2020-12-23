%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6eFSxwJlU7

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:55 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  252 (1122 expanded)
%              Number of leaves         :   50 ( 337 expanded)
%              Depth                    :   36
%              Number of atoms          : 2069 (17351 expanded)
%              Number of equality atoms :   86 ( 693 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t116_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( v1_tsep_1 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k8_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( ( v1_tsep_1 @ B @ A )
                & ( m1_pre_topc @ B @ A ) )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k8_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_tmap_1])).

thf('0',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tsep_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( ( sk_C_1 @ X28 @ X29 )
        = ( u1_struct_0 @ X28 ) )
      | ( v1_tsep_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B_2 @ sk_A )
    | ( ( sk_C_1 @ sk_B_2 @ sk_A )
      = ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tsep_1 @ sk_B_2 @ sk_A )
    | ( ( sk_C_1 @ sk_B_2 @ sk_A )
      = ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( sk_C_1 @ sk_B_2 @ sk_A )
      = ( u1_struct_0 @ sk_B_2 ) )
   <= ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( v3_pre_topc @ ( sk_C_1 @ X28 @ X29 ) @ X29 )
      | ( v1_tsep_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('9',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B_2 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
      | ( v1_tsep_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('14',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('16',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('18',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_tsep_1 @ sk_B_2 @ sk_A )
   <= ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( v1_tsep_1 @ X28 @ X29 )
      | ( X30
       != ( u1_struct_0 @ X28 ) )
      | ( v3_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X28 ) @ X29 )
      | ~ ( v1_tsep_1 @ X28 @ X29 )
      | ~ ( m1_pre_topc @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_tsep_1 @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ( r2_hidden @ X26 @ ( u1_pre_topc @ X27 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('40',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( r2_hidden @ X33 @ ( u1_pre_topc @ X34 ) )
      | ( ( u1_pre_topc @ X34 )
        = ( k5_tmap_1 @ X34 @ X33 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) )
   <= ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t114_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
                    = ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X36 @ X35 ) )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('59',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_2 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('61',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('62',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('70',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_2 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['59','67','75'])).

thf('77',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('78',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X36 @ X35 ) )
        = ( k5_tmap_1 @ X36 @ X37 ) )
      | ( X37
       != ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('79',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X36 @ X35 ) )
        = ( k5_tmap_1 @ X36 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_2 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['76','88'])).

thf('90',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_2 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','89'])).

thf('91',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('92',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_2 )
     != ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
      & ( v1_tsep_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['15','18','93'])).

thf('95',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','94'])).

thf('96',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('97',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( r2_hidden @ X26 @ ( u1_pre_topc @ X27 ) )
      | ( v3_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('102',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( u1_pre_topc @ X34 )
       != ( k5_tmap_1 @ X34 @ X33 ) )
      | ( r2_hidden @ X33 @ ( u1_pre_topc @ X34 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('109',plain,(
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('110',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('111',plain,(
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('112',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['110','114'])).

thf('116',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('117',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('118',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X36 @ X35 ) )
        = ( k5_tmap_1 @ X36 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('126',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( r2_hidden @ X33 @ ( u1_pre_topc @ X34 ) )
      | ( ( u1_pre_topc @ X34 )
        = ( k5_tmap_1 @ X34 @ X33 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

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

thf('131',plain,(
    ! [X23: $i] :
      ( ~ ( v2_pre_topc @ X23 )
      | ( r2_hidden @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('132',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('133',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( r2_hidden @ X26 @ ( u1_pre_topc @ X27 ) )
      | ( v3_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('134',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('142',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ( r2_hidden @ X26 @ ( u1_pre_topc @ X27 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_pre_topc @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['124','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('158',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X36 @ X35 ) )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('162',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('166',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('171',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['168','171'])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['164','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['160','183'])).

thf('185',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['19'])).

thf('186',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v1_tsep_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('187',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['15','18','93','186'])).

thf('188',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['185','187'])).

thf('189',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['184','188','189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k8_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['156','193'])).

thf('195',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_2 ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('196',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','196'])).

thf('198',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['100','198'])).

thf('200',plain,(
    $false ),
    inference(demod,[status(thm)],['95','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6eFSxwJlU7
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 437 iterations in 0.228s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.49/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.49/0.68  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.49/0.68  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.49/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.68  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.49/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.49/0.68  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.49/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.49/0.68  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.49/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.68  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.49/0.68  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.49/0.68  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.49/0.68  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.49/0.68  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.49/0.68  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.49/0.68  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.49/0.68  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.49/0.68  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.49/0.68  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.49/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.68  thf(t116_tmap_1, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.49/0.68           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.49/0.68             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.49/0.68               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.49/0.68            ( l1_pre_topc @ A ) ) =>
% 0.49/0.68          ( ![B:$i]:
% 0.49/0.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.49/0.68              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.49/0.68                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.49/0.68                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.49/0.68  thf('0', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(d1_tsep_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_pre_topc @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.49/0.68           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.49/0.68             ( ![C:$i]:
% 0.49/0.68               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf('1', plain,
% 0.49/0.68      (![X28 : $i, X29 : $i]:
% 0.49/0.68         (~ (m1_pre_topc @ X28 @ X29)
% 0.49/0.68          | ((sk_C_1 @ X28 @ X29) = (u1_struct_0 @ X28))
% 0.49/0.68          | (v1_tsep_1 @ X28 @ X29)
% 0.49/0.68          | ~ (l1_pre_topc @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (v1_tsep_1 @ sk_B_2 @ sk_A)
% 0.49/0.68        | ((sk_C_1 @ sk_B_2 @ sk_A) = (u1_struct_0 @ sk_B_2)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('4', plain,
% 0.49/0.68      (((v1_tsep_1 @ sk_B_2 @ sk_A)
% 0.49/0.68        | ((sk_C_1 @ sk_B_2 @ sk_A) = (u1_struct_0 @ sk_B_2)))),
% 0.49/0.68      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf('5', plain,
% 0.49/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.68          != (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.68        | ~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.49/0.68        | ~ (v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      ((~ (v1_tsep_1 @ sk_B_2 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('split', [status(esa)], ['5'])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      ((((sk_C_1 @ sk_B_2 @ sk_A) = (u1_struct_0 @ sk_B_2)))
% 0.49/0.68         <= (~ ((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['4', '6'])).
% 0.49/0.68  thf('8', plain,
% 0.49/0.68      (![X28 : $i, X29 : $i]:
% 0.49/0.68         (~ (m1_pre_topc @ X28 @ X29)
% 0.49/0.68          | ~ (v3_pre_topc @ (sk_C_1 @ X28 @ X29) @ X29)
% 0.49/0.68          | (v1_tsep_1 @ X28 @ X29)
% 0.49/0.68          | ~ (l1_pre_topc @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)
% 0.49/0.68         | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68         | (v1_tsep_1 @ sk_B_2 @ sk_A)
% 0.49/0.68         | ~ (m1_pre_topc @ sk_B_2 @ sk_A)))
% 0.49/0.68         <= (~ ((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('11', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('12', plain,
% 0.49/0.68      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)
% 0.49/0.68         | (v1_tsep_1 @ sk_B_2 @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      ((~ (v1_tsep_1 @ sk_B_2 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('split', [status(esa)], ['5'])).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A))
% 0.49/0.68         <= (~ ((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('clc', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      (~ ((v1_tsep_1 @ sk_B_2 @ sk_A)) | 
% 0.49/0.68       ~
% 0.49/0.68       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.68          = (k8_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.49/0.68       ~ ((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.49/0.68      inference('split', [status(esa)], ['5'])).
% 0.49/0.68  thf('16', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      ((~ (m1_pre_topc @ sk_B_2 @ sk_A)) <= (~ ((m1_pre_topc @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('split', [status(esa)], ['5'])).
% 0.49/0.68  thf('18', plain, (((m1_pre_topc @ sk_B_2 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.68          = (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.68        | (v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      (((v1_tsep_1 @ sk_B_2 @ sk_A)) <= (((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('split', [status(esa)], ['19'])).
% 0.49/0.68  thf('21', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(t1_tsep_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_pre_topc @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.49/0.68           ( m1_subset_1 @
% 0.49/0.68             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      (![X38 : $i, X39 : $i]:
% 0.49/0.68         (~ (m1_pre_topc @ X38 @ X39)
% 0.49/0.68          | (m1_subset_1 @ (u1_struct_0 @ X38) @ 
% 0.49/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.49/0.68          | ~ (l1_pre_topc @ X39))),
% 0.49/0.68      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.49/0.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.68  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.49/0.68         (~ (m1_pre_topc @ X28 @ X29)
% 0.49/0.68          | ~ (v1_tsep_1 @ X28 @ X29)
% 0.49/0.68          | ((X30) != (u1_struct_0 @ X28))
% 0.49/0.68          | (v3_pre_topc @ X30 @ X29)
% 0.49/0.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.49/0.68          | ~ (l1_pre_topc @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X28 : $i, X29 : $i]:
% 0.49/0.68         (~ (l1_pre_topc @ X29)
% 0.49/0.68          | ~ (m1_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.49/0.68               (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.49/0.68          | (v3_pre_topc @ (u1_struct_0 @ X28) @ X29)
% 0.49/0.68          | ~ (v1_tsep_1 @ X28 @ X29)
% 0.49/0.68          | ~ (m1_pre_topc @ X28 @ X29))),
% 0.49/0.68      inference('simplify', [status(thm)], ['26'])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      ((~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.49/0.68        | ~ (v1_tsep_1 @ sk_B_2 @ sk_A)
% 0.49/0.68        | (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['25', '27'])).
% 0.49/0.68  thf('29', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      ((~ (v1_tsep_1 @ sk_B_2 @ sk_A)
% 0.49/0.68        | (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.49/0.68  thf('32', plain,
% 0.49/0.68      (((v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A))
% 0.49/0.68         <= (((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['20', '31'])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf(d5_pre_topc, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_pre_topc @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68           ( ( v3_pre_topc @ B @ A ) <=>
% 0.49/0.68             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.49/0.68  thf('34', plain,
% 0.49/0.68      (![X26 : $i, X27 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.49/0.68          | ~ (v3_pre_topc @ X26 @ X27)
% 0.49/0.68          | (r2_hidden @ X26 @ (u1_pre_topc @ X27))
% 0.49/0.68          | ~ (l1_pre_topc @ X27))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.49/0.68  thf('35', plain,
% 0.49/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.49/0.68        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (((r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.49/0.68        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['35', '36'])).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      (((r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A)))
% 0.49/0.68         <= (((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['32', '37'])).
% 0.49/0.68  thf('39', plain,
% 0.49/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf(t103_tmap_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.49/0.68             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (![X33 : $i, X34 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.49/0.68          | ~ (r2_hidden @ X33 @ (u1_pre_topc @ X34))
% 0.49/0.68          | ((u1_pre_topc @ X34) = (k5_tmap_1 @ X34 @ X33))
% 0.49/0.68          | ~ (l1_pre_topc @ X34)
% 0.49/0.68          | ~ (v2_pre_topc @ X34)
% 0.49/0.68          | (v2_struct_0 @ X34))),
% 0.49/0.68      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2)))
% 0.49/0.68        | ~ (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.68  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('44', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2)))
% 0.49/0.68        | ~ (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.49/0.68  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('46', plain,
% 0.49/0.68      ((~ (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.49/0.68        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2))))),
% 0.49/0.68      inference('clc', [status(thm)], ['44', '45'])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2))))
% 0.49/0.68         <= (((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['38', '46'])).
% 0.49/0.68  thf('48', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(t114_tmap_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.49/0.68           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.49/0.68             ( ![C:$i]:
% 0.49/0.68               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.49/0.68                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.49/0.68                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf('49', plain,
% 0.49/0.68      (![X35 : $i, X36 : $i]:
% 0.49/0.68         ((v2_struct_0 @ X35)
% 0.49/0.68          | ~ (m1_pre_topc @ X35 @ X36)
% 0.49/0.68          | ((u1_struct_0 @ (k8_tmap_1 @ X36 @ X35)) = (u1_struct_0 @ X36))
% 0.49/0.68          | ~ (l1_pre_topc @ X36)
% 0.49/0.68          | ~ (v2_pre_topc @ X36)
% 0.49/0.68          | (v2_struct_0 @ X36))),
% 0.49/0.68      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.49/0.68  thf('50', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_B_2))),
% 0.49/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.68  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('53', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_B_2))),
% 0.49/0.68      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.49/0.68  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('55', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_B_2)
% 0.49/0.68        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('clc', [status(thm)], ['53', '54'])).
% 0.49/0.68  thf('56', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('57', plain,
% 0.49/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['55', '56'])).
% 0.49/0.68  thf(abstractness_v1_pre_topc, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_pre_topc @ A ) =>
% 0.49/0.68       ( ( v1_pre_topc @ A ) =>
% 0.49/0.68         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.49/0.68  thf('58', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v1_pre_topc @ X0)
% 0.49/0.68          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.49/0.68          | ~ (l1_pre_topc @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.49/0.68  thf('59', plain,
% 0.49/0.68      ((((k8_tmap_1 @ sk_A @ sk_B_2)
% 0.49/0.68          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))))
% 0.49/0.68        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.68        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['57', '58'])).
% 0.49/0.68  thf('60', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(dt_k8_tmap_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.49/0.68         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.49/0.68       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.49/0.68         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.49/0.68         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.49/0.68  thf('61', plain,
% 0.49/0.68      (![X31 : $i, X32 : $i]:
% 0.49/0.68         (~ (l1_pre_topc @ X31)
% 0.49/0.68          | ~ (v2_pre_topc @ X31)
% 0.49/0.68          | (v2_struct_0 @ X31)
% 0.49/0.68          | ~ (m1_pre_topc @ X32 @ X31)
% 0.49/0.68          | (l1_pre_topc @ (k8_tmap_1 @ X31 @ X32)))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.49/0.68  thf('62', plain,
% 0.49/0.68      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.68        | (v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.49/0.68  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('65', plain,
% 0.49/0.68      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.49/0.68  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('67', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))),
% 0.49/0.68      inference('clc', [status(thm)], ['65', '66'])).
% 0.49/0.68  thf('68', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('69', plain,
% 0.49/0.68      (![X31 : $i, X32 : $i]:
% 0.49/0.68         (~ (l1_pre_topc @ X31)
% 0.49/0.68          | ~ (v2_pre_topc @ X31)
% 0.49/0.68          | (v2_struct_0 @ X31)
% 0.49/0.68          | ~ (m1_pre_topc @ X32 @ X31)
% 0.49/0.68          | (v1_pre_topc @ (k8_tmap_1 @ X31 @ X32)))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.49/0.68  thf('70', plain,
% 0.49/0.68      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.68        | (v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['68', '69'])).
% 0.49/0.68  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('73', plain,
% 0.49/0.68      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.49/0.68  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('75', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))),
% 0.49/0.68      inference('clc', [status(thm)], ['73', '74'])).
% 0.49/0.68  thf('76', plain,
% 0.49/0.68      (((k8_tmap_1 @ sk_A @ sk_B_2)
% 0.49/0.68         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))))),
% 0.49/0.68      inference('demod', [status(thm)], ['59', '67', '75'])).
% 0.49/0.68  thf('77', plain,
% 0.49/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('78', plain,
% 0.49/0.68      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.49/0.68         ((v2_struct_0 @ X35)
% 0.49/0.68          | ~ (m1_pre_topc @ X35 @ X36)
% 0.49/0.68          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.49/0.68          | ((u1_pre_topc @ (k8_tmap_1 @ X36 @ X35)) = (k5_tmap_1 @ X36 @ X37))
% 0.49/0.68          | ((X37) != (u1_struct_0 @ X35))
% 0.49/0.68          | ~ (l1_pre_topc @ X36)
% 0.49/0.68          | ~ (v2_pre_topc @ X36)
% 0.49/0.68          | (v2_struct_0 @ X36))),
% 0.49/0.68      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.49/0.68  thf('79', plain,
% 0.49/0.68      (![X35 : $i, X36 : $i]:
% 0.49/0.68         ((v2_struct_0 @ X36)
% 0.49/0.68          | ~ (v2_pre_topc @ X36)
% 0.49/0.68          | ~ (l1_pre_topc @ X36)
% 0.49/0.68          | ((u1_pre_topc @ (k8_tmap_1 @ X36 @ X35))
% 0.49/0.68              = (k5_tmap_1 @ X36 @ (u1_struct_0 @ X35)))
% 0.49/0.68          | ~ (m1_subset_1 @ (u1_struct_0 @ X35) @ 
% 0.49/0.68               (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.49/0.68          | ~ (m1_pre_topc @ X35 @ X36)
% 0.49/0.68          | (v2_struct_0 @ X35))),
% 0.49/0.68      inference('simplify', [status(thm)], ['78'])).
% 0.49/0.68  thf('80', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_B_2)
% 0.49/0.68        | ~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.49/0.68        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.68            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2)))
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['77', '79'])).
% 0.49/0.68  thf('81', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('84', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_B_2)
% 0.49/0.68        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.68            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2)))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.49/0.68  thf('85', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('86', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.68            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2))))),
% 0.49/0.68      inference('clc', [status(thm)], ['84', '85'])).
% 0.49/0.68  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('88', plain,
% 0.49/0.68      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.68         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2)))),
% 0.49/0.68      inference('clc', [status(thm)], ['86', '87'])).
% 0.49/0.68  thf('89', plain,
% 0.49/0.68      (((k8_tmap_1 @ sk_A @ sk_B_2)
% 0.49/0.68         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2))))),
% 0.49/0.68      inference('demod', [status(thm)], ['76', '88'])).
% 0.49/0.68  thf('90', plain,
% 0.49/0.68      ((((k8_tmap_1 @ sk_A @ sk_B_2)
% 0.49/0.68          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.49/0.68         <= (((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['47', '89'])).
% 0.49/0.68  thf('91', plain,
% 0.49/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.68          != (k8_tmap_1 @ sk_A @ sk_B_2)))
% 0.49/0.68         <= (~
% 0.49/0.68             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.68                = (k8_tmap_1 @ sk_A @ sk_B_2))))),
% 0.49/0.68      inference('split', [status(esa)], ['5'])).
% 0.49/0.68  thf('92', plain,
% 0.49/0.68      ((((k8_tmap_1 @ sk_A @ sk_B_2) != (k8_tmap_1 @ sk_A @ sk_B_2)))
% 0.49/0.68         <= (~
% 0.49/0.68             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.68                = (k8_tmap_1 @ sk_A @ sk_B_2))) & 
% 0.49/0.68             ((v1_tsep_1 @ sk_B_2 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['90', '91'])).
% 0.49/0.68  thf('93', plain,
% 0.49/0.68      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.68          = (k8_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.49/0.68       ~ ((v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.49/0.68      inference('simplify', [status(thm)], ['92'])).
% 0.49/0.68  thf('94', plain, (~ ((v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.49/0.68      inference('sat_resolution*', [status(thm)], ['15', '18', '93'])).
% 0.49/0.68  thf('95', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)),
% 0.49/0.68      inference('simpl_trail', [status(thm)], ['14', '94'])).
% 0.49/0.68  thf('96', plain,
% 0.49/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('97', plain,
% 0.49/0.68      (![X26 : $i, X27 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.49/0.68          | ~ (r2_hidden @ X26 @ (u1_pre_topc @ X27))
% 0.49/0.68          | (v3_pre_topc @ X26 @ X27)
% 0.49/0.68          | ~ (l1_pre_topc @ X27))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.49/0.68  thf('98', plain,
% 0.49/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)
% 0.49/0.68        | ~ (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['96', '97'])).
% 0.49/0.68  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('100', plain,
% 0.49/0.68      (((v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)
% 0.49/0.68        | ~ (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['98', '99'])).
% 0.49/0.68  thf('101', plain,
% 0.49/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('102', plain,
% 0.49/0.68      (![X33 : $i, X34 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.49/0.68          | ((u1_pre_topc @ X34) != (k5_tmap_1 @ X34 @ X33))
% 0.49/0.68          | (r2_hidden @ X33 @ (u1_pre_topc @ X34))
% 0.49/0.68          | ~ (l1_pre_topc @ X34)
% 0.49/0.68          | ~ (v2_pre_topc @ X34)
% 0.49/0.68          | (v2_struct_0 @ X34))),
% 0.49/0.68      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.49/0.68  thf('103', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.49/0.68        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['101', '102'])).
% 0.49/0.68  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('106', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.49/0.68        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2))))),
% 0.49/0.68      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.49/0.68  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('108', plain,
% 0.49/0.68      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2)))
% 0.49/0.68        | (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.68      inference('clc', [status(thm)], ['106', '107'])).
% 0.49/0.68  thf(t2_tsep_1, axiom,
% 0.49/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.49/0.68  thf('109', plain,
% 0.49/0.68      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 0.49/0.68      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.49/0.68  thf('110', plain,
% 0.49/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['55', '56'])).
% 0.49/0.68  thf('111', plain,
% 0.49/0.68      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 0.49/0.68      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.49/0.68  thf('112', plain,
% 0.49/0.68      (![X38 : $i, X39 : $i]:
% 0.49/0.68         (~ (m1_pre_topc @ X38 @ X39)
% 0.49/0.68          | (m1_subset_1 @ (u1_struct_0 @ X38) @ 
% 0.49/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.49/0.68          | ~ (l1_pre_topc @ X39))),
% 0.49/0.68      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.49/0.68  thf('113', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (l1_pre_topc @ X0)
% 0.49/0.68          | ~ (l1_pre_topc @ X0)
% 0.49/0.68          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.49/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['111', '112'])).
% 0.49/0.68  thf('114', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.49/0.68           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.49/0.68          | ~ (l1_pre_topc @ X0))),
% 0.49/0.68      inference('simplify', [status(thm)], ['113'])).
% 0.49/0.68  thf('115', plain,
% 0.49/0.68      (((m1_subset_1 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_2)) @ 
% 0.49/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.68        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['110', '114'])).
% 0.49/0.68  thf('116', plain,
% 0.49/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['55', '56'])).
% 0.49/0.68  thf('117', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))),
% 0.49/0.69      inference('clc', [status(thm)], ['65', '66'])).
% 0.49/0.69  thf('118', plain,
% 0.49/0.69      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.49/0.69  thf('119', plain,
% 0.49/0.69      (![X35 : $i, X36 : $i]:
% 0.49/0.69         ((v2_struct_0 @ X36)
% 0.49/0.69          | ~ (v2_pre_topc @ X36)
% 0.49/0.69          | ~ (l1_pre_topc @ X36)
% 0.49/0.69          | ((u1_pre_topc @ (k8_tmap_1 @ X36 @ X35))
% 0.49/0.69              = (k5_tmap_1 @ X36 @ (u1_struct_0 @ X35)))
% 0.49/0.69          | ~ (m1_subset_1 @ (u1_struct_0 @ X35) @ 
% 0.49/0.69               (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.49/0.69          | ~ (m1_pre_topc @ X35 @ X36)
% 0.49/0.69          | (v2_struct_0 @ X35))),
% 0.49/0.69      inference('simplify', [status(thm)], ['78'])).
% 0.49/0.69  thf('120', plain,
% 0.49/0.69      (((v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.49/0.69        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.49/0.69            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.49/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['118', '119'])).
% 0.49/0.69  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('123', plain,
% 0.49/0.69      (((v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.49/0.69        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.49/0.69            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.49/0.69        | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.49/0.69  thf('124', plain,
% 0.49/0.69      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.49/0.69          = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.49/0.69        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('simplify', [status(thm)], ['123'])).
% 0.49/0.69  thf('125', plain,
% 0.49/0.69      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.49/0.69  thf('126', plain,
% 0.49/0.69      (![X33 : $i, X34 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.49/0.69          | ~ (r2_hidden @ X33 @ (u1_pre_topc @ X34))
% 0.49/0.69          | ((u1_pre_topc @ X34) = (k5_tmap_1 @ X34 @ X33))
% 0.49/0.69          | ~ (l1_pre_topc @ X34)
% 0.49/0.69          | ~ (v2_pre_topc @ X34)
% 0.49/0.69          | (v2_struct_0 @ X34))),
% 0.49/0.69      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.49/0.69  thf('127', plain,
% 0.49/0.69      (((v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.49/0.69        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['125', '126'])).
% 0.49/0.69  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('130', plain,
% 0.49/0.69      (((v2_struct_0 @ sk_A)
% 0.49/0.69        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.49/0.69        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.49/0.69  thf(d1_pre_topc, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( l1_pre_topc @ A ) =>
% 0.49/0.69       ( ( v2_pre_topc @ A ) <=>
% 0.49/0.69         ( ( ![B:$i]:
% 0.49/0.69             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69               ( ![C:$i]:
% 0.49/0.69                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.49/0.69                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.49/0.69                     ( r2_hidden @
% 0.49/0.69                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.49/0.69                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.49/0.69           ( ![B:$i]:
% 0.49/0.69             ( ( m1_subset_1 @
% 0.49/0.69                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.69               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.49/0.69                 ( r2_hidden @
% 0.49/0.69                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.49/0.69                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.49/0.69           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.49/0.69  thf(zf_stmt_2, axiom,
% 0.49/0.69    (![B:$i,A:$i]:
% 0.49/0.69     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.49/0.69       ( ( m1_subset_1 @
% 0.49/0.69           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.69         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.49/0.69  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.49/0.69  thf(zf_stmt_4, axiom,
% 0.49/0.69    (![B:$i,A:$i]:
% 0.49/0.69     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.49/0.69       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.49/0.69         ( r2_hidden @
% 0.49/0.69           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.49/0.69  thf(zf_stmt_6, axiom,
% 0.49/0.69    (![B:$i,A:$i]:
% 0.49/0.69     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.49/0.69       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.49/0.69  thf(zf_stmt_8, axiom,
% 0.49/0.69    (![C:$i,B:$i,A:$i]:
% 0.49/0.69     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.49/0.69       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.49/0.69  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.49/0.69  thf(zf_stmt_10, axiom,
% 0.49/0.69    (![C:$i,B:$i,A:$i]:
% 0.49/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.49/0.69       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.49/0.69         ( r2_hidden @
% 0.49/0.69           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.49/0.69  thf(zf_stmt_12, axiom,
% 0.49/0.69    (![C:$i,B:$i,A:$i]:
% 0.49/0.69     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.49/0.69       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.49/0.69         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_13, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( l1_pre_topc @ A ) =>
% 0.49/0.69       ( ( v2_pre_topc @ A ) <=>
% 0.49/0.69         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.49/0.69           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.49/0.69           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.49/0.69  thf('131', plain,
% 0.49/0.69      (![X23 : $i]:
% 0.49/0.69         (~ (v2_pre_topc @ X23)
% 0.49/0.69          | (r2_hidden @ (u1_struct_0 @ X23) @ (u1_pre_topc @ X23))
% 0.49/0.69          | ~ (l1_pre_topc @ X23))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.49/0.69  thf('132', plain,
% 0.49/0.69      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.49/0.69  thf('133', plain,
% 0.49/0.69      (![X26 : $i, X27 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.49/0.69          | ~ (r2_hidden @ X26 @ (u1_pre_topc @ X27))
% 0.49/0.69          | (v3_pre_topc @ X26 @ X27)
% 0.49/0.69          | ~ (l1_pre_topc @ X27))),
% 0.49/0.69      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.49/0.69  thf('134', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.49/0.69        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['132', '133'])).
% 0.49/0.69  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('136', plain,
% 0.49/0.69      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.49/0.69        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['134', '135'])).
% 0.49/0.69  thf('137', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.69        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['131', '136'])).
% 0.49/0.69  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('140', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['137', '138', '139'])).
% 0.49/0.69  thf('141', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.49/0.69           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.49/0.69          | ~ (l1_pre_topc @ X0))),
% 0.49/0.69      inference('simplify', [status(thm)], ['113'])).
% 0.49/0.69  thf('142', plain,
% 0.49/0.69      (![X26 : $i, X27 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.49/0.69          | ~ (v3_pre_topc @ X26 @ X27)
% 0.49/0.69          | (r2_hidden @ X26 @ (u1_pre_topc @ X27))
% 0.49/0.69          | ~ (l1_pre_topc @ X27))),
% 0.49/0.69      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.49/0.69  thf('143', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (l1_pre_topc @ X0)
% 0.49/0.69          | ~ (l1_pre_topc @ X0)
% 0.49/0.69          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.49/0.69          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['141', '142'])).
% 0.49/0.69  thf('144', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.49/0.69          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.49/0.69          | ~ (l1_pre_topc @ X0))),
% 0.49/0.69      inference('simplify', [status(thm)], ['143'])).
% 0.49/0.69  thf('145', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['140', '144'])).
% 0.49/0.69  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('147', plain,
% 0.49/0.69      ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['145', '146'])).
% 0.49/0.69  thf('148', plain,
% 0.49/0.69      (((v2_struct_0 @ sk_A)
% 0.49/0.69        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.49/0.69      inference('demod', [status(thm)], ['130', '147'])).
% 0.49/0.69  thf('149', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('150', plain,
% 0.49/0.69      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('clc', [status(thm)], ['148', '149'])).
% 0.49/0.69  thf('151', plain,
% 0.49/0.69      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A))
% 0.49/0.69        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['124', '150'])).
% 0.49/0.69  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('153', plain,
% 0.49/0.69      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 0.49/0.69        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A)))),
% 0.49/0.69      inference('clc', [status(thm)], ['151', '152'])).
% 0.49/0.69  thf('154', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['109', '153'])).
% 0.49/0.69  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('156', plain,
% 0.49/0.69      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['154', '155'])).
% 0.49/0.69  thf('157', plain,
% 0.49/0.69      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 0.49/0.69      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.49/0.69  thf('158', plain,
% 0.49/0.69      (![X35 : $i, X36 : $i]:
% 0.49/0.69         ((v2_struct_0 @ X35)
% 0.49/0.69          | ~ (m1_pre_topc @ X35 @ X36)
% 0.49/0.69          | ((u1_struct_0 @ (k8_tmap_1 @ X36 @ X35)) = (u1_struct_0 @ X36))
% 0.49/0.69          | ~ (l1_pre_topc @ X36)
% 0.49/0.69          | ~ (v2_pre_topc @ X36)
% 0.49/0.69          | (v2_struct_0 @ X36))),
% 0.49/0.69      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.49/0.69  thf('159', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (l1_pre_topc @ X0)
% 0.49/0.69          | (v2_struct_0 @ X0)
% 0.49/0.69          | ~ (v2_pre_topc @ X0)
% 0.49/0.69          | ~ (l1_pre_topc @ X0)
% 0.49/0.69          | ((u1_struct_0 @ (k8_tmap_1 @ X0 @ X0)) = (u1_struct_0 @ X0))
% 0.49/0.69          | (v2_struct_0 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['157', '158'])).
% 0.49/0.69  thf('160', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (((u1_struct_0 @ (k8_tmap_1 @ X0 @ X0)) = (u1_struct_0 @ X0))
% 0.49/0.69          | ~ (v2_pre_topc @ X0)
% 0.49/0.69          | (v2_struct_0 @ X0)
% 0.49/0.69          | ~ (l1_pre_topc @ X0))),
% 0.49/0.69      inference('simplify', [status(thm)], ['159'])).
% 0.49/0.69  thf('161', plain,
% 0.49/0.69      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 0.49/0.69      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.49/0.69  thf('162', plain,
% 0.49/0.69      (![X31 : $i, X32 : $i]:
% 0.49/0.69         (~ (l1_pre_topc @ X31)
% 0.49/0.69          | ~ (v2_pre_topc @ X31)
% 0.49/0.69          | (v2_struct_0 @ X31)
% 0.49/0.69          | ~ (m1_pre_topc @ X32 @ X31)
% 0.49/0.69          | (v1_pre_topc @ (k8_tmap_1 @ X31 @ X32)))),
% 0.49/0.69      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.49/0.69  thf('163', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (l1_pre_topc @ X0)
% 0.49/0.69          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.49/0.69          | (v2_struct_0 @ X0)
% 0.49/0.69          | ~ (v2_pre_topc @ X0)
% 0.49/0.69          | ~ (l1_pre_topc @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['161', '162'])).
% 0.49/0.69  thf('164', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v2_pre_topc @ X0)
% 0.49/0.69          | (v2_struct_0 @ X0)
% 0.49/0.69          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.49/0.69          | ~ (l1_pre_topc @ X0))),
% 0.49/0.69      inference('simplify', [status(thm)], ['163'])).
% 0.49/0.69  thf('165', plain,
% 0.49/0.69      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 0.49/0.69      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.49/0.69  thf('166', plain,
% 0.49/0.69      (![X31 : $i, X32 : $i]:
% 0.49/0.69         (~ (l1_pre_topc @ X31)
% 0.49/0.69          | ~ (v2_pre_topc @ X31)
% 0.49/0.69          | (v2_struct_0 @ X31)
% 0.49/0.69          | ~ (m1_pre_topc @ X32 @ X31)
% 0.49/0.69          | (l1_pre_topc @ (k8_tmap_1 @ X31 @ X32)))),
% 0.49/0.69      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.49/0.69  thf('167', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (l1_pre_topc @ X0)
% 0.49/0.69          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.49/0.69          | (v2_struct_0 @ X0)
% 0.49/0.69          | ~ (v2_pre_topc @ X0)
% 0.49/0.69          | ~ (l1_pre_topc @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['165', '166'])).
% 0.49/0.69  thf('168', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v2_pre_topc @ X0)
% 0.49/0.69          | (v2_struct_0 @ X0)
% 0.49/0.69          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.49/0.69          | ~ (l1_pre_topc @ X0))),
% 0.49/0.69      inference('simplify', [status(thm)], ['167'])).
% 0.49/0.69  thf('169', plain,
% 0.49/0.69      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['154', '155'])).
% 0.49/0.69  thf('170', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v1_pre_topc @ X0)
% 0.49/0.69          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.49/0.69          | ~ (l1_pre_topc @ X0))),
% 0.49/0.69      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.49/0.69  thf('171', plain,
% 0.49/0.69      ((((k8_tmap_1 @ sk_A @ sk_A)
% 0.49/0.69          = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.49/0.69             (u1_pre_topc @ sk_A)))
% 0.49/0.69        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.49/0.69        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['169', '170'])).
% 0.49/0.69  thf('172', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.69        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.49/0.69        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.49/0.69            = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.49/0.69               (u1_pre_topc @ sk_A))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['168', '171'])).
% 0.49/0.69  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('175', plain,
% 0.49/0.69      (((v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.49/0.69        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.49/0.69            = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.49/0.69               (u1_pre_topc @ sk_A))))),
% 0.49/0.69      inference('demod', [status(thm)], ['172', '173', '174'])).
% 0.49/0.69  thf('176', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('177', plain,
% 0.49/0.69      ((((k8_tmap_1 @ sk_A @ sk_A)
% 0.49/0.69          = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.49/0.69             (u1_pre_topc @ sk_A)))
% 0.49/0.69        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)))),
% 0.49/0.69      inference('clc', [status(thm)], ['175', '176'])).
% 0.49/0.69  thf('178', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.69        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.49/0.69            = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.49/0.69               (u1_pre_topc @ sk_A))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['164', '177'])).
% 0.49/0.69  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('181', plain,
% 0.49/0.69      (((v2_struct_0 @ sk_A)
% 0.49/0.69        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.49/0.69            = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.49/0.69               (u1_pre_topc @ sk_A))))),
% 0.49/0.69      inference('demod', [status(thm)], ['178', '179', '180'])).
% 0.49/0.69  thf('182', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('183', plain,
% 0.49/0.69      (((k8_tmap_1 @ sk_A @ sk_A)
% 0.49/0.69         = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.49/0.69            (u1_pre_topc @ sk_A)))),
% 0.49/0.69      inference('clc', [status(thm)], ['181', '182'])).
% 0.49/0.69  thf('184', plain,
% 0.49/0.69      ((((k8_tmap_1 @ sk_A @ sk_A)
% 0.49/0.69          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.49/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (v2_pre_topc @ sk_A))),
% 0.49/0.69      inference('sup+', [status(thm)], ['160', '183'])).
% 0.49/0.69  thf('185', plain,
% 0.49/0.69      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.69          = (k8_tmap_1 @ sk_A @ sk_B_2)))
% 0.49/0.69         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.69                = (k8_tmap_1 @ sk_A @ sk_B_2))))),
% 0.49/0.69      inference('split', [status(esa)], ['19'])).
% 0.49/0.69  thf('186', plain,
% 0.49/0.69      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.69          = (k8_tmap_1 @ sk_A @ sk_B_2))) | 
% 0.49/0.69       ((v1_tsep_1 @ sk_B_2 @ sk_A))),
% 0.49/0.69      inference('split', [status(esa)], ['19'])).
% 0.49/0.69  thf('187', plain,
% 0.49/0.69      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.69          = (k8_tmap_1 @ sk_A @ sk_B_2)))),
% 0.49/0.69      inference('sat_resolution*', [status(thm)], ['15', '18', '93', '186'])).
% 0.49/0.69  thf('188', plain,
% 0.49/0.69      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.49/0.69         = (k8_tmap_1 @ sk_A @ sk_B_2))),
% 0.49/0.69      inference('simpl_trail', [status(thm)], ['185', '187'])).
% 0.49/0.69  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('190', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('191', plain,
% 0.49/0.69      ((((k8_tmap_1 @ sk_A @ sk_A) = (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.69        | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['184', '188', '189', '190'])).
% 0.49/0.69  thf('192', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('193', plain,
% 0.49/0.69      (((k8_tmap_1 @ sk_A @ sk_A) = (k8_tmap_1 @ sk_A @ sk_B_2))),
% 0.49/0.69      inference('clc', [status(thm)], ['191', '192'])).
% 0.49/0.69  thf('194', plain,
% 0.49/0.69      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2)) = (u1_pre_topc @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['156', '193'])).
% 0.49/0.69  thf('195', plain,
% 0.49/0.69      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_2))
% 0.49/0.69         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2)))),
% 0.49/0.69      inference('clc', [status(thm)], ['86', '87'])).
% 0.49/0.69  thf('196', plain,
% 0.49/0.69      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_2)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['194', '195'])).
% 0.49/0.69  thf('197', plain,
% 0.49/0.69      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.49/0.69        | (r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['108', '196'])).
% 0.49/0.69  thf('198', plain,
% 0.49/0.69      ((r2_hidden @ (u1_struct_0 @ sk_B_2) @ (u1_pre_topc @ sk_A))),
% 0.49/0.69      inference('simplify', [status(thm)], ['197'])).
% 0.49/0.69  thf('199', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_B_2) @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['100', '198'])).
% 0.49/0.69  thf('200', plain, ($false), inference('demod', [status(thm)], ['95', '199'])).
% 0.49/0.69  
% 0.49/0.69  % SZS output end Refutation
% 0.49/0.69  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
