%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KWTX9ZZBJ8

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 464 expanded)
%              Number of leaves         :   29 ( 145 expanded)
%              Depth                    :   27
%              Number of atoms          : 1374 (12694 expanded)
%              Number of equality atoms :   15 ( 211 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t96_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                     => ( D
                        = ( k1_funct_1 @ C @ D ) ) ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                       => ( D
                          = ( k1_funct_1 @ C @ D ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t96_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r2_funct_2 @ A @ B @ C @ D )
          <=> ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X5 @ X3 ) @ X3 )
      | ( r2_funct_2 @ X3 @ X4 @ X5 @ X2 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ X0 @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ X0 @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X14 @ X15 ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('19',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('27',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['16','24','32'])).

thf('34',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ ( u1_struct_0 @ sk_B ) )
      | ( X19
        = ( k1_funct_1 @ sk_C @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t95_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) )
               => ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C )
                  = C ) ) ) ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( u1_struct_0 @ X16 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X17 @ X16 ) @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
        = ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
      = ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
      = ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ( ( k1_funct_1 @ X5 @ ( sk_E @ X2 @ X5 @ X3 ) )
       != ( k1_funct_1 @ X2 @ ( sk_E @ X2 @ X5 @ X3 ) ) )
      | ( r2_funct_2 @ X3 @ X4 @ X5 @ X2 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
       != ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','67'])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['76','77'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('79',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('82',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('86',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['80','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KWTX9ZZBJ8
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:52:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 60 iterations in 0.045s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(t96_tmap_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51               ( ( ![D:$i]:
% 0.21/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 0.21/0.51                 ( r2_funct_2 @
% 0.21/0.51                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.51                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                    ( v1_funct_2 @
% 0.21/0.51                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                    ( m1_subset_1 @
% 0.21/0.51                      C @ 
% 0.21/0.51                      ( k1_zfmisc_1 @
% 0.21/0.51                        ( k2_zfmisc_1 @
% 0.21/0.51                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51                  ( ( ![D:$i]:
% 0.21/0.51                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 0.21/0.51                    ( r2_funct_2 @
% 0.21/0.51                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.51                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k4_tmap_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 0.21/0.51         ( v1_funct_2 @
% 0.21/0.51           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           ( k4_tmap_1 @ A @ B ) @ 
% 0.21/0.51           ( k1_zfmisc_1 @
% 0.21/0.51             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X14)
% 0.21/0.51          | ~ (v2_pre_topc @ X14)
% 0.21/0.51          | (v2_struct_0 @ X14)
% 0.21/0.51          | ~ (m1_pre_topc @ X15 @ X14)
% 0.21/0.51          | (m1_subset_1 @ (k4_tmap_1 @ X14 @ X15) @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14)))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.51  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d9_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51           ( ( r2_funct_2 @ A @ B @ C @ D ) <=>
% 0.21/0.51             ( ![E:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.51                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X2)
% 0.21/0.51          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.21/0.51          | (m1_subset_1 @ (sk_E @ X2 @ X5 @ X3) @ X3)
% 0.21/0.51          | (r2_funct_2 @ X3 @ X4 @ X5 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.21/0.51          | ~ (v1_funct_2 @ X5 @ X3 @ X4)
% 0.21/0.51          | ~ (v1_funct_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.51          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.21/0.51             sk_C)
% 0.21/0.51          | (m1_subset_1 @ (sk_E @ sk_C @ X0 @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.51          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.21/0.51             sk_C)
% 0.21/0.51          | (m1_subset_1 @ (sk_E @ sk_C @ X0 @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((m1_subset_1 @ 
% 0.21/0.51         (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51         (u1_struct_0 @ sk_B))
% 0.21/0.51        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.51        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51             (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '15'])).
% 0.21/0.51  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X14)
% 0.21/0.51          | ~ (v2_pre_topc @ X14)
% 0.21/0.51          | (v2_struct_0 @ X14)
% 0.21/0.51          | ~ (m1_pre_topc @ X15 @ X14)
% 0.21/0.51          | (v1_funct_2 @ (k4_tmap_1 @ X14 @ X15) @ (u1_struct_0 @ X15) @ 
% 0.21/0.51             (u1_struct_0 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51         (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51         (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.51  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51        (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X14)
% 0.21/0.51          | ~ (v2_pre_topc @ X14)
% 0.21/0.51          | (v2_struct_0 @ X14)
% 0.21/0.51          | ~ (m1_pre_topc @ X15 @ X14)
% 0.21/0.51          | (v1_funct_1 @ (k4_tmap_1 @ X14 @ X15)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.51  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (((m1_subset_1 @ 
% 0.21/0.51         (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51         (u1_struct_0 @ sk_B))
% 0.21/0.51        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '24', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((m1_subset_1 @ 
% 0.21/0.51        (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51        (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf(t2_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ X1)
% 0.21/0.51          | (v1_xboole_0 @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (r2_hidden @ 
% 0.21/0.51           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51           (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X19 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X19 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ((X19) = (k1_funct_1 @ sk_C @ X19))
% 0.21/0.51          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ~ (m1_subset_1 @ 
% 0.21/0.51             (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ sk_A))
% 0.21/0.51        | ((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51            = (k1_funct_1 @ sk_C @ 
% 0.21/0.51               (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      ((m1_subset_1 @ 
% 0.21/0.51        (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51        (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf(t55_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X11)
% 0.21/0.51          | ~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.51          | (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.21/0.51          | ~ (l1_pre_topc @ X12)
% 0.21/0.51          | (v2_struct_0 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (m1_subset_1 @ 
% 0.21/0.51             (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (m1_subset_1 @ 
% 0.21/0.51           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51           (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.51  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (m1_subset_1 @ 
% 0.21/0.51           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51           (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ 
% 0.21/0.51           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51           (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      ((m1_subset_1 @ 
% 0.21/0.51        (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51        (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51            = (k1_funct_1 @ sk_C @ 
% 0.21/0.51               (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((m1_subset_1 @ 
% 0.21/0.51        (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51        (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (r2_hidden @ 
% 0.21/0.51           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51           (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf(t95_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X16)
% 0.21/0.51          | ~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.51          | ~ (r2_hidden @ X18 @ (u1_struct_0 @ X16))
% 0.21/0.51          | ((k1_funct_1 @ (k4_tmap_1 @ X17 @ X16) @ X18) = (X18))
% 0.21/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.21/0.51          | ~ (l1_pre_topc @ X17)
% 0.21/0.51          | ~ (v2_pre_topc @ X17)
% 0.21/0.51          | (v2_struct_0 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t95_tmap_1])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ 
% 0.21/0.51               (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.51               (u1_struct_0 @ X0))
% 0.21/0.51          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 0.21/0.51              (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51              = (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.51        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51            = (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '55'])).
% 0.21/0.51  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51            = (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (v1_funct_1 @ X2)
% 0.21/0.51          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.21/0.51          | ((k1_funct_1 @ X5 @ (sk_E @ X2 @ X5 @ X3))
% 0.21/0.51              != (k1_funct_1 @ X2 @ (sk_E @ X2 @ X5 @ X3)))
% 0.21/0.51          | (r2_funct_2 @ X3 @ X4 @ X5 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.21/0.51          | ~ (v1_funct_2 @ X5 @ X3 @ X4)
% 0.21/0.51          | ~ (v1_funct_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51            != (k1_funct_1 @ sk_C @ 
% 0.21/0.51                (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))))
% 0.21/0.51          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51               X0)
% 0.21/0.51          | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 0.21/0.51          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ X0 @ 
% 0.21/0.51             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.51          | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf('63', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.52            != (k1_funct_1 @ sk_C @ 
% 0.21/0.52                (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_B)
% 0.21/0.52          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52               X0)
% 0.21/0.52          | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 0.21/0.52          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ X0 @ 
% 0.21/0.52             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.52            != (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 0.21/0.52          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ X0 @ 
% 0.21/0.52             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.52          | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 0.21/0.52          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52               X0)
% 0.21/0.52          | (v2_struct_0 @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['51', '65'])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_B)
% 0.21/0.52          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52               X0)
% 0.21/0.52          | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 0.21/0.52          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ X0 @ 
% 0.21/0.52             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ X0)
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.52             (k1_zfmisc_1 @ 
% 0.21/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.52        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.52        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52             (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52        (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.52  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['74', '75'])).
% 0.21/0.52  thf('77', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('78', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf(fc2_struct_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (![X10 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.21/0.52          | ~ (l1_struct_0 @ X10)
% 0.21/0.52          | (v2_struct_0 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.52  thf('80', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_m1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('83', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.52  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['83', '84'])).
% 0.21/0.52  thf(dt_l1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.52  thf('86', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.52  thf('88', plain, ((v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['80', '87'])).
% 0.21/0.52  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
