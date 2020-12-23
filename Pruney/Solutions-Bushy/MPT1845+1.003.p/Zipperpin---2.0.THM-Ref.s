%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1845+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sG98RlUt2P

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:24 EST 2020

% Result     : Theorem 2.56s
% Output     : Refutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 864 expanded)
%              Number of leaves         :   42 ( 265 expanded)
%              Depth                    :   26
%              Number of atoms          : 1340 (10705 expanded)
%              Number of equality atoms :   44 ( 734 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(zf_stmt_0,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ( r2_hidden @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(t12_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v2_pre_topc @ A ) )
           => ( v2_pre_topc @ B ) ) ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v2_pre_topc @ A ) )
             => ( v2_pre_topc @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tex_2])).

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X27 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( ( g1_pre_topc @ X30 @ X31 )
       != ( g1_pre_topc @ X28 @ X29 ) )
      | ( X31 = X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B_2 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B_2 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('9',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) )
      | ~ ( zip_tseitin_5 @ ( sk_B_1 @ X24 ) @ X24 )
      | ~ ( zip_tseitin_3 @ ( sk_B @ X24 ) @ X24 )
      | ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('10',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ( v2_pre_topc @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('12',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
    | ( v2_pre_topc @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('14',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X27 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( ( g1_pre_topc @ X30 @ X31 )
       != ( g1_pre_topc @ X28 @ X29 ) )
      | ( X30 = X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_2 )
        = X1 )
      | ~ ( l1_pre_topc @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('19',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('20',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B_2 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v2_pre_topc @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['12','23'])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('28',plain,
    ( ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ( v2_pre_topc @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_pre_topc @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('30',plain,
    ( ~ ( zip_tseitin_3 @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('32',plain,(
    ! [X14: $i,X17: $i] :
      ( ( zip_tseitin_3 @ X14 @ X17 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k3_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('37',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_2 @ X10 @ X12 @ X13 )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('38',plain,(
    ! [X14: $i,X17: $i] :
      ( ( zip_tseitin_3 @ X14 @ X17 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X17 @ X14 ) @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ sk_B_2 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( zip_tseitin_2 @ X16 @ X14 @ X15 )
      | ~ ( zip_tseitin_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_3 @ ( sk_C @ sk_B_2 @ X0 ) @ sk_A )
      | ( zip_tseitin_2 @ X1 @ ( sk_C @ sk_B_2 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ( zip_tseitin_3 @ X25 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('47',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_2 @ X1 @ ( sk_C @ sk_B_2 @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( zip_tseitin_1 @ X10 @ X12 @ X11 )
      | ~ ( zip_tseitin_2 @ X10 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_2 @ X0 @ X1 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_1 @ X1 @ ( sk_C @ sk_B_2 @ X0 ) @ sk_A )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X6 @ X7 @ X9 )
      | ( zip_tseitin_0 @ X6 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('55',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_2 @ X10 @ X12 @ X13 )
      | ~ ( zip_tseitin_1 @ X10 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X14: $i,X17: $i] :
      ( ( zip_tseitin_3 @ X14 @ X17 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X17 @ X14 ) @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ X1 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( u1_pre_topc @ X3 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B_2 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ X1 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('64',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X4 @ X2 @ X5 )
      | ~ ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_0 @ X1 @ ( sk_C @ sk_B_2 @ X0 ) @ sk_A )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X8 ) @ X7 @ X6 ) @ ( u1_pre_topc @ X8 ) )
      | ~ ( zip_tseitin_1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_1 @ X1 @ ( sk_C @ sk_B_2 @ X0 ) @ sk_A )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_2 @ X0 ) @ X1 ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_2 @ X0 ) @ X1 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['52','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_2 @ X0 ) @ X1 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_xboole_0 @ ( sk_C @ sk_B_2 @ X1 ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['35','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k3_xboole_0 @ ( sk_C @ sk_B_2 @ X1 ) @ X0 ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('79',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k3_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( sk_C @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X2 @ ( sk_C @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X6 @ X7 @ X9 )
      | ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X9 ) @ X7 @ X6 ) @ ( u1_pre_topc @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k3_xboole_0 @ X2 @ ( sk_C @ X1 @ X0 ) ) @ ( u1_pre_topc @ X1 ) )
      | ( zip_tseitin_3 @ X0 @ X1 )
      | ( zip_tseitin_1 @ ( sk_C @ X1 @ X0 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k3_xboole_0 @ ( sk_C @ X2 @ X1 ) @ X0 ) @ ( u1_pre_topc @ X2 ) )
      | ( zip_tseitin_1 @ ( sk_C @ X2 @ X1 ) @ X0 @ X2 )
      | ( zip_tseitin_3 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k3_xboole_0 @ ( sk_C @ sk_B_2 @ X1 ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 )
      | ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X1 ) @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 )
      | ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X1 ) @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['75','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ sk_B_2 @ X1 ) @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_2 @ X10 @ X12 @ X13 )
      | ~ ( zip_tseitin_1 @ X10 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X1 @ sk_B_2 )
      | ( zip_tseitin_2 @ ( sk_C @ sk_B_2 @ X1 ) @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X14: $i,X17: $i] :
      ( ( zip_tseitin_3 @ X14 @ X17 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X17 @ X14 ) @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ X0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['30','91'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('94',plain,(
    ! [X21: $i,X23: $i] :
      ( ( zip_tseitin_5 @ X21 @ X23 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( zip_tseitin_5 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ( zip_tseitin_4 @ X21 @ X22 )
      | ~ ( zip_tseitin_5 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_5 @ X0 @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('99',plain,(
    ! [X24: $i,X26: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ( zip_tseitin_5 @ X26 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('102',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_B_2 )
      | ( zip_tseitin_4 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,(
    ~ ( zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['30','91'])).

thf('105',plain,(
    zip_tseitin_4 @ ( sk_B_1 @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('107',plain,(
    ! [X18: $i,X20: $i] :
      ( ( zip_tseitin_4 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( u1_pre_topc @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( u1_pre_topc @ X19 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ ( u1_pre_topc @ X19 ) )
      | ~ ( zip_tseitin_4 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ X0 @ sk_B_2 )
      | ~ ( zip_tseitin_4 @ X0 @ sk_A )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( u1_pre_topc @ sk_B_2 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('112',plain,(
    ! [X18: $i,X20: $i] :
      ( ( zip_tseitin_4 @ X18 @ X20 )
      | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X20 ) @ X18 ) @ ( u1_pre_topc @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_B_2 ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( u1_struct_0 @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ X0 @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['110','115'])).

thf('117',plain,(
    zip_tseitin_4 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['105','116'])).

thf('118',plain,(
    ! [X21: $i,X23: $i] :
      ( ( zip_tseitin_5 @ X21 @ X23 )
      | ~ ( zip_tseitin_4 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('119',plain,(
    zip_tseitin_5 @ ( sk_B_1 @ sk_B_2 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['92','119'])).


%------------------------------------------------------------------------------
