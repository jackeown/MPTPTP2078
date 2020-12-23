%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dEo9KfFcUZ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:10 EST 2020

% Result     : Theorem 10.69s
% Output     : Refutation 10.82s
% Verified   : 
% Statistics : Number of formulae       :  281 ( 956 expanded)
%              Number of leaves         :   36 ( 297 expanded)
%              Depth                    :   35
%              Number of atoms          : 5415 (36145 expanded)
%              Number of equality atoms :   50 ( 443 expanded)
%              Maximal formula depth    :   32 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t139_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( A
                      = ( k1_tsep_1 @ A @ C @ D ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ E @ ( k10_tmap_1 @ A @ B @ C @ D @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( A
                        = ( k1_tsep_1 @ A @ C @ D ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ E @ ( k10_tmap_1 @ A @ B @ C @ D @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( r1_funct_2 @ X9 @ X10 @ X13 @ X11 @ X8 @ X12 )
      | ( X8 != X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r1_funct_2 @ X9 @ X10 @ X13 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X11 )
      | ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X30 @ X31 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20','23','24','25'])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X30 @ X31 @ X29 @ X32 ) @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('33',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X30 @ X31 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf(dt_k10_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A )
        & ~ ( v2_struct_0 @ D )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
        & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X24 @ X27 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X3 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X3 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_funct_1 @ ( k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','67','68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('78',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['71','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20','23','24','25'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20','23','24','25'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('88',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X24 @ X27 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X27 @ X24 @ X26 ) ) @ ( u1_struct_0 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X0 @ X1 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X0 @ X1 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ X0 @ X2 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ X0 @ X2 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['85','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X0 @ X1 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X0 @ X1 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['82','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','106'])).

thf('108',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['76','77'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t138_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ E @ ( k10_tmap_1 @ A @ B @ C @ D @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ X35 @ X36 @ X34 ) ) @ ( u1_struct_0 @ X33 ) @ X37 @ ( k10_tmap_1 @ X35 @ X33 @ X36 @ X34 @ ( k3_tmap_1 @ X35 @ X33 @ ( k1_tsep_1 @ X35 @ X36 @ X34 ) @ X36 @ X37 ) @ ( k3_tmap_1 @ X35 @ X33 @ ( k1_tsep_1 @ X35 @ X36 @ X34 ) @ X34 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X35 @ X36 @ X34 ) ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ ( k1_tsep_1 @ X35 @ X36 @ X34 ) ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t138_tmap_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ X1 ) @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1 ) @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120','121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('128',plain,(
    ! [X38: $i] :
      ( ( m1_pre_topc @ X38 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('129',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('130',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( ( k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) @ X22 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('150',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( k2_tmap_1 @ X16 @ X14 @ X17 @ X15 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X17 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152','153','154','155','156','157'])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['147','163'])).

thf('165',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152','153','154','155','156','157'])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['171','178'])).

thf('180',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','126','164','179','180','181'])).

thf('183',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20','23','24','25'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20','23','24','25'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('191',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X24 @ X27 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X27 @ X24 @ X26 ) ) @ ( u1_struct_0 @ X25 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X0 @ X1 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X0 @ X1 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ X0 @ X2 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['189','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ X0 @ X2 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['188','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['187','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X0 @ X1 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X0 @ X1 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['185','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['184','204'])).

thf('206',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('207',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['205','206','207','208'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['183','209'])).

thf('211',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['76','77'])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('215',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['213','219'])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['182','220'])).

thf('222',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['110','222'])).

thf('224',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['79','224'])).

thf('226',plain,
    ( ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['226','229'])).

thf('231',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','230'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('232',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('233',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('235',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,(
    $false ),
    inference(demod,[status(thm)],['0','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dEo9KfFcUZ
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.69/11.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.69/11.00  % Solved by: fo/fo7.sh
% 10.69/11.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.69/11.00  % done 8280 iterations in 10.557s
% 10.69/11.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.69/11.00  % SZS output start Refutation
% 10.69/11.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.69/11.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.69/11.00  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 10.69/11.00  thf(sk_E_type, type, sk_E: $i).
% 10.69/11.00  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 10.69/11.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.69/11.00  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 10.69/11.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.69/11.00  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 10.69/11.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.69/11.00  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 10.69/11.00  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 10.69/11.00  thf(sk_C_type, type, sk_C: $i).
% 10.69/11.00  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 10.69/11.00  thf(sk_D_type, type, sk_D: $i).
% 10.69/11.00  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 10.69/11.00  thf(sk_B_type, type, sk_B: $i).
% 10.69/11.00  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 10.69/11.00  thf(sk_A_type, type, sk_A: $i).
% 10.69/11.00  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 10.69/11.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.69/11.00  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 10.69/11.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.69/11.00  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 10.69/11.00  thf(t139_tmap_1, conjecture,
% 10.69/11.00    (![A:$i]:
% 10.69/11.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.69/11.00       ( ![B:$i]:
% 10.69/11.00         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 10.69/11.00             ( l1_pre_topc @ B ) ) =>
% 10.69/11.00           ( ![C:$i]:
% 10.69/11.00             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 10.69/11.00               ( ![D:$i]:
% 10.69/11.00                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 10.69/11.00                   ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 10.69/11.00                     ( ![E:$i]:
% 10.69/11.00                       ( ( ( v1_funct_1 @ E ) & 
% 10.69/11.00                           ( v1_funct_2 @
% 10.69/11.00                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 10.69/11.00                           ( m1_subset_1 @
% 10.69/11.00                             E @ 
% 10.69/11.00                             ( k1_zfmisc_1 @
% 10.69/11.00                               ( k2_zfmisc_1 @
% 10.69/11.00                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 10.69/11.00                         ( r1_funct_2 @
% 10.69/11.00                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 10.69/11.00                           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 10.69/11.00                           ( u1_struct_0 @ B ) @ E @ 
% 10.69/11.00                           ( k10_tmap_1 @
% 10.69/11.00                             A @ B @ C @ D @ ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 10.69/11.00                             ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 10.69/11.00  thf(zf_stmt_0, negated_conjecture,
% 10.69/11.00    (~( ![A:$i]:
% 10.69/11.00        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 10.69/11.00            ( l1_pre_topc @ A ) ) =>
% 10.69/11.00          ( ![B:$i]:
% 10.69/11.00            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 10.69/11.00                ( l1_pre_topc @ B ) ) =>
% 10.69/11.00              ( ![C:$i]:
% 10.69/11.00                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 10.69/11.00                  ( ![D:$i]:
% 10.69/11.00                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 10.69/11.00                      ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 10.69/11.00                        ( ![E:$i]:
% 10.69/11.00                          ( ( ( v1_funct_1 @ E ) & 
% 10.69/11.00                              ( v1_funct_2 @
% 10.69/11.00                                E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 10.69/11.00                              ( m1_subset_1 @
% 10.69/11.00                                E @ 
% 10.69/11.00                                ( k1_zfmisc_1 @
% 10.69/11.00                                  ( k2_zfmisc_1 @
% 10.69/11.00                                    ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 10.69/11.00                            ( r1_funct_2 @
% 10.69/11.00                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 10.69/11.00                              ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 10.69/11.00                              ( u1_struct_0 @ B ) @ E @ 
% 10.69/11.00                              ( k10_tmap_1 @
% 10.69/11.00                                A @ B @ C @ D @ 
% 10.69/11.00                                ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 10.69/11.00                                ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 10.69/11.00    inference('cnf.neg', [status(esa)], [t139_tmap_1])).
% 10.69/11.00  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('1', plain,
% 10.69/11.00      ((m1_subset_1 @ sk_E @ 
% 10.69/11.00        (k1_zfmisc_1 @ 
% 10.69/11.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('2', plain,
% 10.69/11.00      ((m1_subset_1 @ sk_E @ 
% 10.69/11.00        (k1_zfmisc_1 @ 
% 10.69/11.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf(redefinition_r1_funct_2, axiom,
% 10.69/11.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.69/11.00     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 10.69/11.00         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 10.69/11.00         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.69/11.00         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 10.69/11.00         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.69/11.00       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 10.69/11.00  thf('3', plain,
% 10.69/11.00      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 10.69/11.00         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 10.69/11.00          | ~ (v1_funct_2 @ X8 @ X9 @ X10)
% 10.69/11.00          | ~ (v1_funct_1 @ X8)
% 10.69/11.00          | (v1_xboole_0 @ X11)
% 10.69/11.00          | (v1_xboole_0 @ X10)
% 10.69/11.00          | ~ (v1_funct_1 @ X12)
% 10.69/11.00          | ~ (v1_funct_2 @ X12 @ X13 @ X11)
% 10.69/11.00          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 10.69/11.00          | (r1_funct_2 @ X9 @ X10 @ X13 @ X11 @ X8 @ X12)
% 10.69/11.00          | ((X8) != (X12)))),
% 10.69/11.00      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 10.69/11.00  thf('4', plain,
% 10.69/11.00      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 10.69/11.00         ((r1_funct_2 @ X9 @ X10 @ X13 @ X11 @ X12 @ X12)
% 10.69/11.00          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 10.69/11.00          | ~ (v1_funct_2 @ X12 @ X13 @ X11)
% 10.69/11.00          | (v1_xboole_0 @ X10)
% 10.69/11.00          | (v1_xboole_0 @ X11)
% 10.69/11.00          | ~ (v1_funct_1 @ X12)
% 10.69/11.00          | ~ (v1_funct_2 @ X12 @ X9 @ X10)
% 10.69/11.00          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 10.69/11.00      inference('simplify', [status(thm)], ['3'])).
% 10.69/11.00  thf('5', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i]:
% 10.69/11.00         (~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 10.69/11.00          | ~ (v1_funct_2 @ sk_E @ X1 @ X0)
% 10.69/11.00          | ~ (v1_funct_1 @ sk_E)
% 10.69/11.00          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | (v1_xboole_0 @ X0)
% 10.69/11.00          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 10.69/11.00             (u1_struct_0 @ sk_B) @ sk_E @ sk_E))),
% 10.69/11.00      inference('sup-', [status(thm)], ['2', '4'])).
% 10.69/11.00  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('7', plain,
% 10.69/11.00      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('8', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i]:
% 10.69/11.00         (~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 10.69/11.00          | ~ (v1_funct_2 @ sk_E @ X1 @ X0)
% 10.69/11.00          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | (v1_xboole_0 @ X0)
% 10.69/11.00          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 10.69/11.00             (u1_struct_0 @ sk_B) @ sk_E @ sk_E))),
% 10.69/11.00      inference('demod', [status(thm)], ['5', '6', '7'])).
% 10.69/11.00  thf('9', plain,
% 10.69/11.00      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.69/11.00         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)
% 10.69/11.00        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 10.69/11.00        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 10.69/11.00        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 10.69/11.00      inference('sup-', [status(thm)], ['1', '8'])).
% 10.69/11.00  thf('10', plain,
% 10.69/11.00      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('11', plain,
% 10.69/11.00      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.69/11.00         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)
% 10.69/11.00        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 10.69/11.00        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 10.69/11.00      inference('demod', [status(thm)], ['9', '10'])).
% 10.69/11.00  thf('12', plain,
% 10.69/11.00      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 10.69/11.00        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.69/11.00           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E))),
% 10.69/11.00      inference('simplify', [status(thm)], ['11'])).
% 10.69/11.00  thf('13', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('14', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('15', plain,
% 10.69/11.00      ((m1_subset_1 @ sk_E @ 
% 10.69/11.00        (k1_zfmisc_1 @ 
% 10.69/11.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf(dt_k2_tmap_1, axiom,
% 10.69/11.00    (![A:$i,B:$i,C:$i,D:$i]:
% 10.69/11.00     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 10.69/11.00         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 10.69/11.00         ( m1_subset_1 @
% 10.69/11.00           C @ 
% 10.69/11.00           ( k1_zfmisc_1 @
% 10.69/11.00             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 10.69/11.00         ( l1_struct_0 @ D ) ) =>
% 10.69/11.00       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 10.69/11.00         ( v1_funct_2 @
% 10.69/11.00           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 10.69/11.00           ( u1_struct_0 @ B ) ) & 
% 10.69/11.00         ( m1_subset_1 @
% 10.69/11.00           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 10.69/11.00           ( k1_zfmisc_1 @
% 10.69/11.00             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 10.69/11.00  thf('16', plain,
% 10.69/11.00      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 10.69/11.00         (~ (m1_subset_1 @ X29 @ 
% 10.69/11.00             (k1_zfmisc_1 @ 
% 10.69/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 10.69/11.00          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 10.69/11.00          | ~ (v1_funct_1 @ X29)
% 10.69/11.00          | ~ (l1_struct_0 @ X31)
% 10.69/11.00          | ~ (l1_struct_0 @ X30)
% 10.69/11.00          | ~ (l1_struct_0 @ X32)
% 10.69/11.00          | (v1_funct_1 @ (k2_tmap_1 @ X30 @ X31 @ X29 @ X32)))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 10.69/11.00  thf('17', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (l1_struct_0 @ X0)
% 10.69/11.00          | ~ (l1_struct_0 @ sk_A)
% 10.69/11.00          | ~ (l1_struct_0 @ sk_B)
% 10.69/11.00          | ~ (v1_funct_1 @ sk_E)
% 10.69/11.00          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 10.69/11.00      inference('sup-', [status(thm)], ['15', '16'])).
% 10.69/11.00  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf(dt_l1_pre_topc, axiom,
% 10.69/11.00    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 10.69/11.00  thf('19', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.69/11.00  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 10.69/11.00      inference('sup-', [status(thm)], ['18', '19'])).
% 10.69/11.00  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('22', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.69/11.00  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 10.69/11.00      inference('sup-', [status(thm)], ['21', '22'])).
% 10.69/11.00  thf('24', plain, ((v1_funct_1 @ sk_E)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('25', plain,
% 10.69/11.00      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('26', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['17', '20', '23', '24', '25'])).
% 10.69/11.00  thf('27', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['17', '20', '23', '24', '25'])).
% 10.69/11.00  thf('28', plain,
% 10.69/11.00      ((m1_subset_1 @ sk_E @ 
% 10.69/11.00        (k1_zfmisc_1 @ 
% 10.69/11.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('29', plain,
% 10.69/11.00      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 10.69/11.00         (~ (m1_subset_1 @ X29 @ 
% 10.69/11.00             (k1_zfmisc_1 @ 
% 10.69/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 10.69/11.00          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 10.69/11.00          | ~ (v1_funct_1 @ X29)
% 10.69/11.00          | ~ (l1_struct_0 @ X31)
% 10.69/11.00          | ~ (l1_struct_0 @ X30)
% 10.69/11.00          | ~ (l1_struct_0 @ X32)
% 10.69/11.00          | (v1_funct_2 @ (k2_tmap_1 @ X30 @ X31 @ X29 @ X32) @ 
% 10.69/11.00             (u1_struct_0 @ X32) @ (u1_struct_0 @ X31)))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 10.69/11.00  thf('30', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (l1_struct_0 @ X0)
% 10.69/11.00          | ~ (l1_struct_0 @ sk_A)
% 10.69/11.00          | ~ (l1_struct_0 @ sk_B)
% 10.69/11.00          | ~ (v1_funct_1 @ sk_E)
% 10.69/11.00          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 10.69/11.00      inference('sup-', [status(thm)], ['28', '29'])).
% 10.69/11.00  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 10.69/11.00      inference('sup-', [status(thm)], ['18', '19'])).
% 10.69/11.00  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 10.69/11.00      inference('sup-', [status(thm)], ['21', '22'])).
% 10.69/11.00  thf('33', plain, ((v1_funct_1 @ sk_E)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('34', plain,
% 10.69/11.00      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('35', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 10.69/11.00  thf('36', plain,
% 10.69/11.00      ((m1_subset_1 @ sk_E @ 
% 10.69/11.00        (k1_zfmisc_1 @ 
% 10.69/11.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('37', plain,
% 10.69/11.00      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 10.69/11.00         (~ (m1_subset_1 @ X29 @ 
% 10.69/11.00             (k1_zfmisc_1 @ 
% 10.69/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 10.69/11.00          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 10.69/11.00          | ~ (v1_funct_1 @ X29)
% 10.69/11.00          | ~ (l1_struct_0 @ X31)
% 10.69/11.00          | ~ (l1_struct_0 @ X30)
% 10.69/11.00          | ~ (l1_struct_0 @ X32)
% 10.69/11.00          | (m1_subset_1 @ (k2_tmap_1 @ X30 @ X31 @ X29 @ X32) @ 
% 10.69/11.00             (k1_zfmisc_1 @ 
% 10.69/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31)))))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 10.69/11.00  thf('38', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (k1_zfmisc_1 @ 
% 10.69/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (l1_struct_0 @ X0)
% 10.69/11.00          | ~ (l1_struct_0 @ sk_A)
% 10.69/11.00          | ~ (l1_struct_0 @ sk_B)
% 10.69/11.00          | ~ (v1_funct_1 @ sk_E)
% 10.69/11.00          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 10.69/11.00      inference('sup-', [status(thm)], ['36', '37'])).
% 10.69/11.00  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 10.69/11.00      inference('sup-', [status(thm)], ['18', '19'])).
% 10.69/11.00  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 10.69/11.00      inference('sup-', [status(thm)], ['21', '22'])).
% 10.69/11.00  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('42', plain,
% 10.69/11.00      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('43', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (k1_zfmisc_1 @ 
% 10.69/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 10.69/11.00  thf('44', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 10.69/11.00  thf('45', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (k1_zfmisc_1 @ 
% 10.69/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 10.69/11.00  thf(dt_k10_tmap_1, axiom,
% 10.69/11.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.69/11.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 10.69/11.00         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 10.69/11.00         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 10.69/11.00         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 10.69/11.00         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 10.69/11.00         ( v1_funct_1 @ E ) & 
% 10.69/11.00         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 10.69/11.00         ( m1_subset_1 @
% 10.69/11.00           E @ 
% 10.69/11.00           ( k1_zfmisc_1 @
% 10.69/11.00             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 10.69/11.00         ( v1_funct_1 @ F ) & 
% 10.69/11.00         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 10.69/11.00         ( m1_subset_1 @
% 10.69/11.00           F @ 
% 10.69/11.00           ( k1_zfmisc_1 @
% 10.69/11.00             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 10.69/11.00       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 10.69/11.00         ( v1_funct_2 @
% 10.69/11.00           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 10.69/11.00           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 10.69/11.00         ( m1_subset_1 @
% 10.69/11.00           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 10.69/11.00           ( k1_zfmisc_1 @
% 10.69/11.00             ( k2_zfmisc_1 @
% 10.69/11.00               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 10.69/11.00               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 10.69/11.00  thf('46', plain,
% 10.69/11.00      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 10.69/11.00         (~ (m1_subset_1 @ X23 @ 
% 10.69/11.00             (k1_zfmisc_1 @ 
% 10.69/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 10.69/11.00          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 10.69/11.00          | ~ (v1_funct_1 @ X23)
% 10.69/11.00          | ~ (m1_pre_topc @ X26 @ X27)
% 10.69/11.00          | (v2_struct_0 @ X26)
% 10.69/11.00          | ~ (m1_pre_topc @ X24 @ X27)
% 10.69/11.00          | (v2_struct_0 @ X24)
% 10.69/11.00          | ~ (l1_pre_topc @ X25)
% 10.69/11.00          | ~ (v2_pre_topc @ X25)
% 10.69/11.00          | (v2_struct_0 @ X25)
% 10.69/11.00          | ~ (l1_pre_topc @ X27)
% 10.69/11.00          | ~ (v2_pre_topc @ X27)
% 10.69/11.00          | (v2_struct_0 @ X27)
% 10.69/11.00          | ~ (v1_funct_1 @ X28)
% 10.69/11.00          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 10.69/11.00          | ~ (m1_subset_1 @ X28 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 10.69/11.00          | (v1_funct_1 @ (k10_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28)))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 10.69/11.00  thf('47', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X3 @ sk_B @ X0 @ X2 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X1))
% 10.69/11.00          | ~ (m1_subset_1 @ X1 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (v1_funct_1 @ X1)
% 10.69/11.00          | (v2_struct_0 @ X3)
% 10.69/11.00          | ~ (v2_pre_topc @ X3)
% 10.69/11.00          | ~ (l1_pre_topc @ X3)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | ~ (v2_pre_topc @ sk_B)
% 10.69/11.00          | ~ (l1_pre_topc @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X3)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (m1_pre_topc @ X2 @ X3)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 10.69/11.00      inference('sup-', [status(thm)], ['45', '46'])).
% 10.69/11.00  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('50', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X3 @ sk_B @ X0 @ X2 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X1))
% 10.69/11.00          | ~ (m1_subset_1 @ X1 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (v1_funct_1 @ X1)
% 10.69/11.00          | (v2_struct_0 @ X3)
% 10.69/11.00          | ~ (v2_pre_topc @ X3)
% 10.69/11.00          | ~ (l1_pre_topc @ X3)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X3)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (m1_pre_topc @ X2 @ X3)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 10.69/11.00      inference('demod', [status(thm)], ['47', '48', '49'])).
% 10.69/11.00  thf('51', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (m1_pre_topc @ X2 @ X1)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X1)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | ~ (l1_pre_topc @ X1)
% 10.69/11.00          | ~ (v2_pre_topc @ X1)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (v1_funct_1 @ X3)
% 10.69/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('sup-', [status(thm)], ['44', '50'])).
% 10.69/11.00  thf('52', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.69/11.00         ((v1_funct_1 @ 
% 10.69/11.00           (k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 10.69/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3))
% 10.69/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (v1_funct_1 @ X3)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (v2_pre_topc @ X1)
% 10.69/11.00          | ~ (l1_pre_topc @ X1)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X1)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (m1_pre_topc @ X2 @ X1)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('simplify', [status(thm)], ['51'])).
% 10.69/11.00  thf('53', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | ~ (l1_struct_0 @ X1)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))))),
% 10.69/11.00      inference('sup-', [status(thm)], ['43', '52'])).
% 10.69/11.00  thf('54', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.69/11.00          | ~ (l1_struct_0 @ X1)
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('sup-', [status(thm)], ['35', '53'])).
% 10.69/11.00  thf('55', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X1)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('simplify', [status(thm)], ['54'])).
% 10.69/11.00  thf('56', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | ~ (l1_struct_0 @ X1)
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)))
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('sup-', [status(thm)], ['27', '55'])).
% 10.69/11.00  thf('57', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.69/11.00         (~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)))
% 10.69/11.00          | ~ (l1_struct_0 @ X1)
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('simplify', [status(thm)], ['56'])).
% 10.69/11.00  thf('58', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | ~ (l1_struct_0 @ X1)
% 10.69/11.00          | ~ (l1_struct_0 @ X0)
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X2))),
% 10.69/11.00      inference('sup-', [status(thm)], ['26', '57'])).
% 10.69/11.00  thf('59', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.69/11.00         (~ (m1_pre_topc @ X0 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))
% 10.69/11.00          | ~ (l1_struct_0 @ X1)
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('simplify', [status(thm)], ['58'])).
% 10.69/11.00  thf('60', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ sk_D)
% 10.69/11.00          | ~ (l1_struct_0 @ X0)
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.69/11.00          | (v2_struct_0 @ sk_A)
% 10.69/11.00          | ~ (v2_pre_topc @ sk_A)
% 10.69/11.00          | ~ (l1_pre_topc @ sk_A)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.69/11.00          | (v2_struct_0 @ sk_D))),
% 10.69/11.00      inference('sup-', [status(thm)], ['14', '59'])).
% 10.69/11.00  thf('61', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf(dt_m1_pre_topc, axiom,
% 10.69/11.00    (![A:$i]:
% 10.69/11.00     ( ( l1_pre_topc @ A ) =>
% 10.69/11.00       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 10.69/11.00  thf('62', plain,
% 10.69/11.00      (![X5 : $i, X6 : $i]:
% 10.69/11.00         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 10.69/11.00  thf('63', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 10.69/11.00      inference('sup-', [status(thm)], ['61', '62'])).
% 10.69/11.00  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('65', plain, ((l1_pre_topc @ sk_D)),
% 10.69/11.00      inference('demod', [status(thm)], ['63', '64'])).
% 10.69/11.00  thf('66', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.69/11.00  thf('67', plain, ((l1_struct_0 @ sk_D)),
% 10.69/11.00      inference('sup-', [status(thm)], ['65', '66'])).
% 10.69/11.00  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('70', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | (v1_funct_1 @ 
% 10.69/11.00             (k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.69/11.00          | (v2_struct_0 @ sk_A)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.69/11.00          | (v2_struct_0 @ sk_D))),
% 10.69/11.00      inference('demod', [status(thm)], ['60', '67', '68', '69'])).
% 10.69/11.00  thf('71', plain,
% 10.69/11.00      (((v2_struct_0 @ sk_D)
% 10.69/11.00        | (v2_struct_0 @ sk_C)
% 10.69/11.00        | (v2_struct_0 @ sk_B)
% 10.69/11.00        | (v2_struct_0 @ sk_A)
% 10.69/11.00        | (v1_funct_1 @ 
% 10.69/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.69/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.69/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.69/11.00        | ~ (l1_struct_0 @ sk_C))),
% 10.69/11.00      inference('sup-', [status(thm)], ['13', '70'])).
% 10.69/11.00  thf('72', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('73', plain,
% 10.69/11.00      (![X5 : $i, X6 : $i]:
% 10.69/11.00         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 10.69/11.00  thf('74', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 10.69/11.00      inference('sup-', [status(thm)], ['72', '73'])).
% 10.69/11.00  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('76', plain, ((l1_pre_topc @ sk_C)),
% 10.69/11.00      inference('demod', [status(thm)], ['74', '75'])).
% 10.69/11.00  thf('77', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.69/11.00  thf('78', plain, ((l1_struct_0 @ sk_C)),
% 10.69/11.00      inference('sup-', [status(thm)], ['76', '77'])).
% 10.69/11.00  thf('79', plain,
% 10.69/11.00      (((v2_struct_0 @ sk_D)
% 10.69/11.00        | (v2_struct_0 @ sk_C)
% 10.69/11.00        | (v2_struct_0 @ sk_B)
% 10.69/11.00        | (v2_struct_0 @ sk_A)
% 10.69/11.00        | (v1_funct_1 @ 
% 10.69/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.69/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.69/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 10.69/11.00      inference('demod', [status(thm)], ['71', '78'])).
% 10.69/11.00  thf('80', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('81', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('82', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['17', '20', '23', '24', '25'])).
% 10.69/11.00  thf('83', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['17', '20', '23', '24', '25'])).
% 10.69/11.00  thf('84', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 10.69/11.00  thf('85', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (k1_zfmisc_1 @ 
% 10.69/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 10.69/11.00  thf('86', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 10.69/11.00  thf('87', plain,
% 10.69/11.00      (![X0 : $i]:
% 10.69/11.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00           (k1_zfmisc_1 @ 
% 10.69/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 10.69/11.00  thf('88', plain,
% 10.69/11.00      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 10.69/11.00         (~ (m1_subset_1 @ X23 @ 
% 10.69/11.00             (k1_zfmisc_1 @ 
% 10.69/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 10.69/11.00          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 10.69/11.00          | ~ (v1_funct_1 @ X23)
% 10.69/11.00          | ~ (m1_pre_topc @ X26 @ X27)
% 10.69/11.00          | (v2_struct_0 @ X26)
% 10.69/11.00          | ~ (m1_pre_topc @ X24 @ X27)
% 10.69/11.00          | (v2_struct_0 @ X24)
% 10.69/11.00          | ~ (l1_pre_topc @ X25)
% 10.69/11.00          | ~ (v2_pre_topc @ X25)
% 10.69/11.00          | (v2_struct_0 @ X25)
% 10.69/11.00          | ~ (l1_pre_topc @ X27)
% 10.69/11.00          | ~ (v2_pre_topc @ X27)
% 10.69/11.00          | (v2_struct_0 @ X27)
% 10.69/11.00          | ~ (v1_funct_1 @ X28)
% 10.69/11.00          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 10.69/11.00          | ~ (m1_subset_1 @ X28 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 10.69/11.00          | (v1_funct_2 @ (k10_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28) @ 
% 10.69/11.00             (u1_struct_0 @ (k1_tsep_1 @ X27 @ X24 @ X26)) @ 
% 10.69/11.00             (u1_struct_0 @ X25)))),
% 10.69/11.00      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 10.69/11.00  thf('89', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | (v1_funct_2 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3) @ 
% 10.69/11.00             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X0 @ X1)) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (v1_funct_1 @ X3)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | ~ (v2_pre_topc @ sk_B)
% 10.69/11.00          | ~ (l1_pre_topc @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 10.69/11.00      inference('sup-', [status(thm)], ['87', '88'])).
% 10.69/11.00  thf('90', plain, ((v2_pre_topc @ sk_B)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 10.69/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.69/11.00  thf('92', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | (v1_funct_2 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3) @ 
% 10.69/11.00             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X0 @ X1)) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (v1_funct_1 @ X3)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 10.69/11.00      inference('demod', [status(thm)], ['89', '90', '91'])).
% 10.69/11.00  thf('93', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (m1_pre_topc @ X2 @ X1)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X1)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | ~ (l1_pre_topc @ X1)
% 10.69/11.00          | ~ (v2_pre_topc @ X1)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (v1_funct_1 @ X3)
% 10.69/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | (v1_funct_2 @ 
% 10.69/11.00             (k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 10.69/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3) @ 
% 10.69/11.00             (u1_struct_0 @ (k1_tsep_1 @ X1 @ X0 @ X2)) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('sup-', [status(thm)], ['86', '92'])).
% 10.69/11.00  thf('94', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.69/11.00         ((v1_funct_2 @ 
% 10.69/11.00           (k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 10.69/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3) @ 
% 10.69/11.00           (u1_struct_0 @ (k1_tsep_1 @ X1 @ X0 @ X2)) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.69/11.00               (k1_zfmisc_1 @ 
% 10.69/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))))
% 10.69/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | ~ (v1_funct_1 @ X3)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | ~ (v2_pre_topc @ X1)
% 10.69/11.00          | ~ (l1_pre_topc @ X1)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X1)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (m1_pre_topc @ X2 @ X1)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (l1_struct_0 @ X0))),
% 10.69/11.00      inference('simplify', [status(thm)], ['93'])).
% 10.69/11.00  thf('95', plain,
% 10.69/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.69/11.00         (~ (l1_struct_0 @ X0)
% 10.69/11.00          | ~ (l1_struct_0 @ X1)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.69/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X0)
% 10.69/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.69/11.00          | (v2_struct_0 @ X1)
% 10.69/11.00          | (v2_struct_0 @ sk_B)
% 10.69/11.00          | ~ (l1_pre_topc @ X2)
% 10.69/11.00          | ~ (v2_pre_topc @ X2)
% 10.69/11.00          | (v2_struct_0 @ X2)
% 10.69/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.69/11.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.69/11.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.69/11.00          | (v1_funct_2 @ 
% 10.69/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ (u1_struct_0 @ sk_B)))),
% 10.82/11.00      inference('sup-', [status(thm)], ['85', '94'])).
% 10.82/11.00  thf('96', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('sup-', [status(thm)], ['84', '95'])).
% 10.82/11.00  thf('97', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('simplify', [status(thm)], ['96'])).
% 10.82/11.00  thf('98', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)) @ 
% 10.82/11.00             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X0 @ X1)) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('sup-', [status(thm)], ['83', '97'])).
% 10.82/11.00  thf('99', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.82/11.00          | (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)) @ 
% 10.82/11.00             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X0 @ X1)) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('simplify', [status(thm)], ['98'])).
% 10.82/11.00  thf('100', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (l1_struct_0 @ X0)
% 10.82/11.00          | (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2))),
% 10.82/11.00      inference('sup-', [status(thm)], ['82', '99'])).
% 10.82/11.00  thf('101', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('simplify', [status(thm)], ['100'])).
% 10.82/11.00  thf('102', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ sk_D)
% 10.82/11.00          | ~ (l1_struct_0 @ X0)
% 10.82/11.00          | (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ sk_D)) @ 
% 10.82/11.00             (u1_struct_0 @ sk_B))
% 10.82/11.00          | (v2_struct_0 @ sk_A)
% 10.82/11.00          | ~ (v2_pre_topc @ sk_A)
% 10.82/11.00          | ~ (l1_pre_topc @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_D))),
% 10.82/11.00      inference('sup-', [status(thm)], ['81', '101'])).
% 10.82/11.00  thf('103', plain, ((l1_struct_0 @ sk_D)),
% 10.82/11.00      inference('sup-', [status(thm)], ['65', '66'])).
% 10.82/11.00  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('106', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ sk_D)) @ 
% 10.82/11.00             (u1_struct_0 @ sk_B))
% 10.82/11.00          | (v2_struct_0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_D))),
% 10.82/11.00      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 10.82/11.00  thf('107', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_A)
% 10.82/11.00        | (v1_funct_2 @ 
% 10.82/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 10.82/11.00           (u1_struct_0 @ sk_B))
% 10.82/11.00        | ~ (l1_struct_0 @ sk_C))),
% 10.82/11.00      inference('sup-', [status(thm)], ['80', '106'])).
% 10.82/11.00  thf('108', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('109', plain, ((l1_struct_0 @ sk_C)),
% 10.82/11.00      inference('sup-', [status(thm)], ['76', '77'])).
% 10.82/11.00  thf('110', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_A)
% 10.82/11.00        | (v1_funct_2 @ 
% 10.82/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 10.82/11.00      inference('demod', [status(thm)], ['107', '108', '109'])).
% 10.82/11.00  thf('111', plain,
% 10.82/11.00      ((m1_subset_1 @ sk_E @ 
% 10.82/11.00        (k1_zfmisc_1 @ 
% 10.82/11.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('112', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf(t138_tmap_1, axiom,
% 10.82/11.00    (![A:$i]:
% 10.82/11.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.82/11.00       ( ![B:$i]:
% 10.82/11.00         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 10.82/11.00             ( l1_pre_topc @ B ) ) =>
% 10.82/11.00           ( ![C:$i]:
% 10.82/11.00             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 10.82/11.00               ( ![D:$i]:
% 10.82/11.00                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 10.82/11.00                   ( ![E:$i]:
% 10.82/11.00                     ( ( ( v1_funct_1 @ E ) & 
% 10.82/11.00                         ( v1_funct_2 @
% 10.82/11.00                           E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 10.82/11.00                           ( u1_struct_0 @ B ) ) & 
% 10.82/11.00                         ( m1_subset_1 @
% 10.82/11.00                           E @ 
% 10.82/11.00                           ( k1_zfmisc_1 @
% 10.82/11.00                             ( k2_zfmisc_1 @
% 10.82/11.00                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 10.82/11.00                               ( u1_struct_0 @ B ) ) ) ) ) =>
% 10.82/11.00                       ( r2_funct_2 @
% 10.82/11.00                         ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 10.82/11.00                         ( u1_struct_0 @ B ) @ E @ 
% 10.82/11.00                         ( k10_tmap_1 @
% 10.82/11.00                           A @ B @ C @ D @ 
% 10.82/11.00                           ( k3_tmap_1 @
% 10.82/11.00                             A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 10.82/11.00                           ( k3_tmap_1 @
% 10.82/11.00                             A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 10.82/11.00  thf('113', plain,
% 10.82/11.00      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 10.82/11.00         ((v2_struct_0 @ X33)
% 10.82/11.00          | ~ (v2_pre_topc @ X33)
% 10.82/11.00          | ~ (l1_pre_topc @ X33)
% 10.82/11.00          | (v2_struct_0 @ X34)
% 10.82/11.00          | ~ (m1_pre_topc @ X34 @ X35)
% 10.82/11.00          | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ X35 @ X36 @ X34)) @ 
% 10.82/11.00             (u1_struct_0 @ X33) @ X37 @ 
% 10.82/11.00             (k10_tmap_1 @ X35 @ X33 @ X36 @ X34 @ 
% 10.82/11.00              (k3_tmap_1 @ X35 @ X33 @ (k1_tsep_1 @ X35 @ X36 @ X34) @ X36 @ 
% 10.82/11.00               X37) @ 
% 10.82/11.00              (k3_tmap_1 @ X35 @ X33 @ (k1_tsep_1 @ X35 @ X36 @ X34) @ X34 @ 
% 10.82/11.00               X37)))
% 10.82/11.00          | ~ (m1_subset_1 @ X37 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X35 @ X36 @ X34)) @ 
% 10.82/11.00                 (u1_struct_0 @ X33))))
% 10.82/11.00          | ~ (v1_funct_2 @ X37 @ 
% 10.82/11.00               (u1_struct_0 @ (k1_tsep_1 @ X35 @ X36 @ X34)) @ 
% 10.82/11.00               (u1_struct_0 @ X33))
% 10.82/11.00          | ~ (v1_funct_1 @ X37)
% 10.82/11.00          | ~ (m1_pre_topc @ X36 @ X35)
% 10.82/11.00          | (v2_struct_0 @ X36)
% 10.82/11.00          | ~ (l1_pre_topc @ X35)
% 10.82/11.00          | ~ (v2_pre_topc @ X35)
% 10.82/11.00          | (v2_struct_0 @ X35))),
% 10.82/11.00      inference('cnf', [status(esa)], [t138_tmap_1])).
% 10.82/11.00  thf('114', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i]:
% 10.82/11.00         (~ (m1_subset_1 @ X1 @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 10.82/11.00          | (v2_struct_0 @ sk_A)
% 10.82/11.00          | ~ (v2_pre_topc @ sk_A)
% 10.82/11.00          | ~ (l1_pre_topc @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_C)
% 10.82/11.00          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 10.82/11.00          | ~ (v1_funct_1 @ X1)
% 10.82/11.00          | ~ (v1_funct_2 @ X1 @ 
% 10.82/11.00               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 10.82/11.00               (u1_struct_0 @ X0))
% 10.82/11.00          | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 10.82/11.00             (u1_struct_0 @ X0) @ X1 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ 
% 10.82/11.00              (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 10.82/11.00               sk_C @ X1) @ 
% 10.82/11.00              (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 10.82/11.00               sk_D @ X1)))
% 10.82/11.00          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_D)
% 10.82/11.00          | ~ (l1_pre_topc @ X0)
% 10.82/11.00          | ~ (v2_pre_topc @ X0)
% 10.82/11.00          | (v2_struct_0 @ X0))),
% 10.82/11.00      inference('sup-', [status(thm)], ['112', '113'])).
% 10.82/11.00  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('117', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('118', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('119', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('120', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('121', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('122', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('123', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i]:
% 10.82/11.00         (~ (m1_subset_1 @ X1 @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 10.82/11.00          | (v2_struct_0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_C)
% 10.82/11.00          | ~ (v1_funct_1 @ X1)
% 10.82/11.00          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 10.82/11.00          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ 
% 10.82/11.00              (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1) @ 
% 10.82/11.00              (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1)))
% 10.82/11.00          | (v2_struct_0 @ sk_D)
% 10.82/11.00          | ~ (l1_pre_topc @ X0)
% 10.82/11.00          | ~ (v2_pre_topc @ X0)
% 10.82/11.00          | (v2_struct_0 @ X0))),
% 10.82/11.00      inference('demod', [status(thm)],
% 10.82/11.00                ['114', '115', '116', '117', '118', '119', '120', '121', '122'])).
% 10.82/11.00  thf('124', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_B)
% 10.82/11.00        | ~ (v2_pre_topc @ sk_B)
% 10.82/11.00        | ~ (l1_pre_topc @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 10.82/11.00            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 10.82/11.00        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 10.82/11.00        | ~ (v1_funct_1 @ sk_E)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('sup-', [status(thm)], ['111', '123'])).
% 10.82/11.00  thf('125', plain, ((v2_pre_topc @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('126', plain, ((l1_pre_topc @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('127', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf(t2_tsep_1, axiom,
% 10.82/11.00    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 10.82/11.00  thf('128', plain,
% 10.82/11.00      (![X38 : $i]: ((m1_pre_topc @ X38 @ X38) | ~ (l1_pre_topc @ X38))),
% 10.82/11.00      inference('cnf', [status(esa)], [t2_tsep_1])).
% 10.82/11.00  thf('129', plain,
% 10.82/11.00      ((m1_subset_1 @ sk_E @ 
% 10.82/11.00        (k1_zfmisc_1 @ 
% 10.82/11.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf(d5_tmap_1, axiom,
% 10.82/11.00    (![A:$i]:
% 10.82/11.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.82/11.00       ( ![B:$i]:
% 10.82/11.00         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 10.82/11.00             ( l1_pre_topc @ B ) ) =>
% 10.82/11.00           ( ![C:$i]:
% 10.82/11.00             ( ( m1_pre_topc @ C @ A ) =>
% 10.82/11.00               ( ![D:$i]:
% 10.82/11.00                 ( ( m1_pre_topc @ D @ A ) =>
% 10.82/11.00                   ( ![E:$i]:
% 10.82/11.00                     ( ( ( v1_funct_1 @ E ) & 
% 10.82/11.00                         ( v1_funct_2 @
% 10.82/11.00                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 10.82/11.00                         ( m1_subset_1 @
% 10.82/11.00                           E @ 
% 10.82/11.00                           ( k1_zfmisc_1 @
% 10.82/11.00                             ( k2_zfmisc_1 @
% 10.82/11.00                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 10.82/11.00                       ( ( m1_pre_topc @ D @ C ) =>
% 10.82/11.00                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 10.82/11.00                           ( k2_partfun1 @
% 10.82/11.00                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 10.82/11.00                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 10.82/11.00  thf('130', plain,
% 10.82/11.00      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 10.82/11.00         ((v2_struct_0 @ X18)
% 10.82/11.00          | ~ (v2_pre_topc @ X18)
% 10.82/11.00          | ~ (l1_pre_topc @ X18)
% 10.82/11.00          | ~ (m1_pre_topc @ X19 @ X20)
% 10.82/11.00          | ~ (m1_pre_topc @ X19 @ X21)
% 10.82/11.00          | ((k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 10.82/11.00                 X22 @ (u1_struct_0 @ X19)))
% 10.82/11.00          | ~ (m1_subset_1 @ X22 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))))
% 10.82/11.00          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))
% 10.82/11.00          | ~ (v1_funct_1 @ X22)
% 10.82/11.00          | ~ (m1_pre_topc @ X21 @ X20)
% 10.82/11.00          | ~ (l1_pre_topc @ X20)
% 10.82/11.00          | ~ (v2_pre_topc @ X20)
% 10.82/11.00          | (v2_struct_0 @ X20))),
% 10.82/11.00      inference('cnf', [status(esa)], [d5_tmap_1])).
% 10.82/11.00  thf('131', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i]:
% 10.82/11.00         ((v2_struct_0 @ X0)
% 10.82/11.00          | ~ (v2_pre_topc @ X0)
% 10.82/11.00          | ~ (l1_pre_topc @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ sk_A @ X0)
% 10.82/11.00          | ~ (v1_funct_1 @ sk_E)
% 10.82/11.00          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00                 sk_E @ (u1_struct_0 @ X1)))
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ sk_A)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X0)
% 10.82/11.00          | ~ (l1_pre_topc @ sk_B)
% 10.82/11.00          | ~ (v2_pre_topc @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ sk_B))),
% 10.82/11.00      inference('sup-', [status(thm)], ['129', '130'])).
% 10.82/11.00  thf('132', plain, ((v1_funct_1 @ sk_E)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('133', plain,
% 10.82/11.00      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('134', plain, ((l1_pre_topc @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('135', plain, ((v2_pre_topc @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('136', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i]:
% 10.82/11.00         ((v2_struct_0 @ X0)
% 10.82/11.00          | ~ (v2_pre_topc @ X0)
% 10.82/11.00          | ~ (l1_pre_topc @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ sk_A @ X0)
% 10.82/11.00          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00                 sk_E @ (u1_struct_0 @ X1)))
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ sk_A)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X0)
% 10.82/11.00          | (v2_struct_0 @ sk_B))),
% 10.82/11.00      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 10.82/11.00  thf('137', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         (~ (l1_pre_topc @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00                 sk_E @ (u1_struct_0 @ X0)))
% 10.82/11.00          | ~ (l1_pre_topc @ sk_A)
% 10.82/11.00          | ~ (v2_pre_topc @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('sup-', [status(thm)], ['128', '136'])).
% 10.82/11.00  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('141', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00                 sk_E @ (u1_struct_0 @ X0)))
% 10.82/11.00          | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 10.82/11.00  thf('142', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v2_struct_0 @ sk_A)
% 10.82/11.00          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00                 sk_E @ (u1_struct_0 @ X0)))
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_B))),
% 10.82/11.00      inference('simplify', [status(thm)], ['141'])).
% 10.82/11.00  thf('143', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_B)
% 10.82/11.00        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 10.82/11.00            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00               sk_E @ (u1_struct_0 @ sk_C)))
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('sup-', [status(thm)], ['127', '142'])).
% 10.82/11.00  thf('144', plain, (~ (v2_struct_0 @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('145', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 10.82/11.00            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00               sk_E @ (u1_struct_0 @ sk_C))))),
% 10.82/11.00      inference('clc', [status(thm)], ['143', '144'])).
% 10.82/11.00  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('147', plain,
% 10.82/11.00      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 10.82/11.00         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00            (u1_struct_0 @ sk_C)))),
% 10.82/11.00      inference('clc', [status(thm)], ['145', '146'])).
% 10.82/11.00  thf('148', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('149', plain,
% 10.82/11.00      ((m1_subset_1 @ sk_E @ 
% 10.82/11.00        (k1_zfmisc_1 @ 
% 10.82/11.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf(d4_tmap_1, axiom,
% 10.82/11.00    (![A:$i]:
% 10.82/11.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.82/11.00       ( ![B:$i]:
% 10.82/11.00         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 10.82/11.00             ( l1_pre_topc @ B ) ) =>
% 10.82/11.00           ( ![C:$i]:
% 10.82/11.00             ( ( ( v1_funct_1 @ C ) & 
% 10.82/11.00                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 10.82/11.00                 ( m1_subset_1 @
% 10.82/11.00                   C @ 
% 10.82/11.00                   ( k1_zfmisc_1 @
% 10.82/11.00                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 10.82/11.00               ( ![D:$i]:
% 10.82/11.00                 ( ( m1_pre_topc @ D @ A ) =>
% 10.82/11.00                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 10.82/11.00                     ( k2_partfun1 @
% 10.82/11.00                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 10.82/11.00                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 10.82/11.00  thf('150', plain,
% 10.82/11.00      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 10.82/11.00         ((v2_struct_0 @ X14)
% 10.82/11.00          | ~ (v2_pre_topc @ X14)
% 10.82/11.00          | ~ (l1_pre_topc @ X14)
% 10.82/11.00          | ~ (m1_pre_topc @ X15 @ X16)
% 10.82/11.00          | ((k2_tmap_1 @ X16 @ X14 @ X17 @ X15)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14) @ 
% 10.82/11.00                 X17 @ (u1_struct_0 @ X15)))
% 10.82/11.00          | ~ (m1_subset_1 @ X17 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))))
% 10.82/11.00          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))
% 10.82/11.00          | ~ (v1_funct_1 @ X17)
% 10.82/11.00          | ~ (l1_pre_topc @ X16)
% 10.82/11.00          | ~ (v2_pre_topc @ X16)
% 10.82/11.00          | (v2_struct_0 @ X16))),
% 10.82/11.00      inference('cnf', [status(esa)], [d4_tmap_1])).
% 10.82/11.00  thf('151', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v2_struct_0 @ sk_A)
% 10.82/11.00          | ~ (v2_pre_topc @ sk_A)
% 10.82/11.00          | ~ (l1_pre_topc @ sk_A)
% 10.82/11.00          | ~ (v1_funct_1 @ sk_E)
% 10.82/11.00          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00                 sk_E @ (u1_struct_0 @ X0)))
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | ~ (l1_pre_topc @ sk_B)
% 10.82/11.00          | ~ (v2_pre_topc @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ sk_B))),
% 10.82/11.00      inference('sup-', [status(thm)], ['149', '150'])).
% 10.82/11.00  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('154', plain, ((v1_funct_1 @ sk_E)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('155', plain,
% 10.82/11.00      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('156', plain, ((l1_pre_topc @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('157', plain, ((v2_pre_topc @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('158', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v2_struct_0 @ sk_A)
% 10.82/11.00          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00                 sk_E @ (u1_struct_0 @ X0)))
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_B))),
% 10.82/11.00      inference('demod', [status(thm)],
% 10.82/11.00                ['151', '152', '153', '154', '155', '156', '157'])).
% 10.82/11.00  thf('159', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_B)
% 10.82/11.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 10.82/11.00            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00               sk_E @ (u1_struct_0 @ sk_C)))
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('sup-', [status(thm)], ['148', '158'])).
% 10.82/11.00  thf('160', plain, (~ (v2_struct_0 @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('161', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 10.82/11.00            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00               sk_E @ (u1_struct_0 @ sk_C))))),
% 10.82/11.00      inference('clc', [status(thm)], ['159', '160'])).
% 10.82/11.00  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('163', plain,
% 10.82/11.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 10.82/11.00         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00            (u1_struct_0 @ sk_C)))),
% 10.82/11.00      inference('clc', [status(thm)], ['161', '162'])).
% 10.82/11.00  thf('164', plain,
% 10.82/11.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 10.82/11.00         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 10.82/11.00      inference('sup+', [status(thm)], ['147', '163'])).
% 10.82/11.00  thf('165', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('166', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v2_struct_0 @ sk_A)
% 10.82/11.00          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00                 sk_E @ (u1_struct_0 @ X0)))
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_B))),
% 10.82/11.00      inference('simplify', [status(thm)], ['141'])).
% 10.82/11.00  thf('167', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_B)
% 10.82/11.00        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 10.82/11.00            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00               sk_E @ (u1_struct_0 @ sk_D)))
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('sup-', [status(thm)], ['165', '166'])).
% 10.82/11.00  thf('168', plain, (~ (v2_struct_0 @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('169', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 10.82/11.00            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00               sk_E @ (u1_struct_0 @ sk_D))))),
% 10.82/11.00      inference('clc', [status(thm)], ['167', '168'])).
% 10.82/11.00  thf('170', plain, (~ (v2_struct_0 @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('171', plain,
% 10.82/11.00      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 10.82/11.00         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00            (u1_struct_0 @ sk_D)))),
% 10.82/11.00      inference('clc', [status(thm)], ['169', '170'])).
% 10.82/11.00  thf('172', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('173', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v2_struct_0 @ sk_A)
% 10.82/11.00          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 10.82/11.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00                 sk_E @ (u1_struct_0 @ X0)))
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_B))),
% 10.82/11.00      inference('demod', [status(thm)],
% 10.82/11.00                ['151', '152', '153', '154', '155', '156', '157'])).
% 10.82/11.00  thf('174', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_B)
% 10.82/11.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 10.82/11.00            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00               sk_E @ (u1_struct_0 @ sk_D)))
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('sup-', [status(thm)], ['172', '173'])).
% 10.82/11.00  thf('175', plain, (~ (v2_struct_0 @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('176', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 10.82/11.00            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00               sk_E @ (u1_struct_0 @ sk_D))))),
% 10.82/11.00      inference('clc', [status(thm)], ['174', '175'])).
% 10.82/11.00  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('178', plain,
% 10.82/11.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 10.82/11.00         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00            (u1_struct_0 @ sk_D)))),
% 10.82/11.00      inference('clc', [status(thm)], ['176', '177'])).
% 10.82/11.00  thf('179', plain,
% 10.82/11.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 10.82/11.00         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 10.82/11.00      inference('sup+', [status(thm)], ['171', '178'])).
% 10.82/11.00  thf('180', plain,
% 10.82/11.00      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('181', plain, ((v1_funct_1 @ sk_E)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('182', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('demod', [status(thm)],
% 10.82/11.00                ['124', '125', '126', '164', '179', '180', '181'])).
% 10.82/11.00  thf('183', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('184', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('185', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('demod', [status(thm)], ['17', '20', '23', '24', '25'])).
% 10.82/11.00  thf('186', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('demod', [status(thm)], ['17', '20', '23', '24', '25'])).
% 10.82/11.00  thf('187', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 10.82/11.00  thf('188', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00           (k1_zfmisc_1 @ 
% 10.82/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 10.82/11.00  thf('189', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 10.82/11.00  thf('190', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00           (k1_zfmisc_1 @ 
% 10.82/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 10.82/11.00  thf('191', plain,
% 10.82/11.00      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 10.82/11.00         (~ (m1_subset_1 @ X23 @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 10.82/11.00          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 10.82/11.00          | ~ (v1_funct_1 @ X23)
% 10.82/11.00          | ~ (m1_pre_topc @ X26 @ X27)
% 10.82/11.00          | (v2_struct_0 @ X26)
% 10.82/11.00          | ~ (m1_pre_topc @ X24 @ X27)
% 10.82/11.00          | (v2_struct_0 @ X24)
% 10.82/11.00          | ~ (l1_pre_topc @ X25)
% 10.82/11.00          | ~ (v2_pre_topc @ X25)
% 10.82/11.00          | (v2_struct_0 @ X25)
% 10.82/11.00          | ~ (l1_pre_topc @ X27)
% 10.82/11.00          | ~ (v2_pre_topc @ X27)
% 10.82/11.00          | (v2_struct_0 @ X27)
% 10.82/11.00          | ~ (v1_funct_1 @ X28)
% 10.82/11.00          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 10.82/11.00          | ~ (m1_subset_1 @ X28 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 10.82/11.00          | (m1_subset_1 @ (k10_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X27 @ X24 @ X26)) @ 
% 10.82/11.00               (u1_struct_0 @ X25)))))),
% 10.82/11.00      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 10.82/11.00  thf('192', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X0 @ X1)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (v1_funct_1 @ X3)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (v2_pre_topc @ sk_B)
% 10.82/11.00          | ~ (l1_pre_topc @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 10.82/11.00      inference('sup-', [status(thm)], ['190', '191'])).
% 10.82/11.00  thf('193', plain, ((v2_pre_topc @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('194', plain, ((l1_pre_topc @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('195', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X0 @ X1)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (v1_funct_1 @ X3)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 10.82/11.00      inference('demod', [status(thm)], ['192', '193', '194'])).
% 10.82/11.00  thf('196', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | ~ (m1_pre_topc @ X2 @ X1)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X1)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (l1_pre_topc @ X1)
% 10.82/11.00          | ~ (v2_pre_topc @ X1)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (v1_funct_1 @ X3)
% 10.82/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))))
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ X0 @ X2)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('sup-', [status(thm)], ['189', '195'])).
% 10.82/11.00  thf('197', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.82/11.00         ((m1_subset_1 @ 
% 10.82/11.00           (k10_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ X3) @ 
% 10.82/11.00           (k1_zfmisc_1 @ 
% 10.82/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ X0 @ X2)) @ 
% 10.82/11.00             (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (m1_subset_1 @ X3 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (v1_funct_1 @ X3)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (v2_pre_topc @ X1)
% 10.82/11.00          | ~ (l1_pre_topc @ X1)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X1)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (m1_pre_topc @ X2 @ X1)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('simplify', [status(thm)], ['196'])).
% 10.82/11.00  thf('198', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B)))))),
% 10.82/11.00      inference('sup-', [status(thm)], ['188', '197'])).
% 10.82/11.00  thf('199', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('sup-', [status(thm)], ['187', '198'])).
% 10.82/11.00  thf('200', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('simplify', [status(thm)], ['199'])).
% 10.82/11.00  thf('201', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X0 @ X1)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('sup-', [status(thm)], ['186', '200'])).
% 10.82/11.00  thf('202', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X0 @ X1)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('simplify', [status(thm)], ['201'])).
% 10.82/11.00  thf('203', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (l1_struct_0 @ X0)
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ X2))),
% 10.82/11.00      inference('sup-', [status(thm)], ['185', '202'])).
% 10.82/11.00  thf('204', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.82/11.00         (~ (m1_pre_topc @ X0 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X1 @ X2)
% 10.82/11.00          | (v2_struct_0 @ X1)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | ~ (l1_pre_topc @ X2)
% 10.82/11.00          | ~ (v2_pre_topc @ X2)
% 10.82/11.00          | (v2_struct_0 @ X2)
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ X2 @ sk_B @ X1 @ X0 @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X1 @ X0)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (l1_struct_0 @ X1)
% 10.82/11.00          | ~ (l1_struct_0 @ X0))),
% 10.82/11.00      inference('simplify', [status(thm)], ['203'])).
% 10.82/11.00  thf('205', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ sk_D)
% 10.82/11.00          | ~ (l1_struct_0 @ X0)
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ sk_D)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | (v2_struct_0 @ sk_A)
% 10.82/11.00          | ~ (v2_pre_topc @ sk_A)
% 10.82/11.00          | ~ (l1_pre_topc @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_D))),
% 10.82/11.00      inference('sup-', [status(thm)], ['184', '204'])).
% 10.82/11.00  thf('206', plain, ((l1_struct_0 @ sk_D)),
% 10.82/11.00      inference('sup-', [status(thm)], ['65', '66'])).
% 10.82/11.00  thf('207', plain, ((v2_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('208', plain, ((l1_pre_topc @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('209', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         (~ (l1_struct_0 @ X0)
% 10.82/11.00          | (m1_subset_1 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ X0 @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00             (k1_zfmisc_1 @ 
% 10.82/11.00              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ sk_D)) @ 
% 10.82/11.00               (u1_struct_0 @ sk_B))))
% 10.82/11.00          | (v2_struct_0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_B)
% 10.82/11.00          | (v2_struct_0 @ X0)
% 10.82/11.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 10.82/11.00          | (v2_struct_0 @ sk_D))),
% 10.82/11.00      inference('demod', [status(thm)], ['205', '206', '207', '208'])).
% 10.82/11.00  thf('210', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_A)
% 10.82/11.00        | (m1_subset_1 @ 
% 10.82/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00           (k1_zfmisc_1 @ 
% 10.82/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 10.82/11.00             (u1_struct_0 @ sk_B))))
% 10.82/11.00        | ~ (l1_struct_0 @ sk_C))),
% 10.82/11.00      inference('sup-', [status(thm)], ['183', '209'])).
% 10.82/11.00  thf('211', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('212', plain, ((l1_struct_0 @ sk_C)),
% 10.82/11.00      inference('sup-', [status(thm)], ['76', '77'])).
% 10.82/11.00  thf('213', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_A)
% 10.82/11.00        | (m1_subset_1 @ 
% 10.82/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00           (k1_zfmisc_1 @ 
% 10.82/11.00            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 10.82/11.00      inference('demod', [status(thm)], ['210', '211', '212'])).
% 10.82/11.00  thf('214', plain,
% 10.82/11.00      ((m1_subset_1 @ sk_E @ 
% 10.82/11.00        (k1_zfmisc_1 @ 
% 10.82/11.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf(redefinition_r2_funct_2, axiom,
% 10.82/11.00    (![A:$i,B:$i,C:$i,D:$i]:
% 10.82/11.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.82/11.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.82/11.00         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.82/11.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.82/11.00       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.82/11.00  thf('215', plain,
% 10.82/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.82/11.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 10.82/11.00          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 10.82/11.00          | ~ (v1_funct_1 @ X0)
% 10.82/11.00          | ~ (v1_funct_1 @ X3)
% 10.82/11.00          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 10.82/11.00          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 10.82/11.00          | ((X0) = (X3))
% 10.82/11.00          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 10.82/11.00      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 10.82/11.00  thf('216', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00             X0)
% 10.82/11.00          | ((sk_E) = (X0))
% 10.82/11.00          | ~ (m1_subset_1 @ X0 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (v1_funct_1 @ X0)
% 10.82/11.00          | ~ (v1_funct_1 @ sk_E)
% 10.82/11.00          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 10.82/11.00      inference('sup-', [status(thm)], ['214', '215'])).
% 10.82/11.00  thf('217', plain, ((v1_funct_1 @ sk_E)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('218', plain,
% 10.82/11.00      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('219', plain,
% 10.82/11.00      (![X0 : $i]:
% 10.82/11.00         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00             X0)
% 10.82/11.00          | ((sk_E) = (X0))
% 10.82/11.00          | ~ (m1_subset_1 @ X0 @ 
% 10.82/11.00               (k1_zfmisc_1 @ 
% 10.82/11.00                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 10.82/11.00          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 10.82/11.00          | ~ (v1_funct_1 @ X0))),
% 10.82/11.00      inference('demod', [status(thm)], ['216', '217', '218'])).
% 10.82/11.00  thf('220', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | ~ (v1_funct_1 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | ~ (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 10.82/11.00        | ((sk_E)
% 10.82/11.00            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 10.82/11.00      inference('sup-', [status(thm)], ['213', '219'])).
% 10.82/11.00  thf('221', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | ((sk_E)
% 10.82/11.00            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | ~ (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 10.82/11.00        | ~ (v1_funct_1 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('sup-', [status(thm)], ['182', '220'])).
% 10.82/11.00  thf('222', plain,
% 10.82/11.00      ((~ (v1_funct_1 @ 
% 10.82/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | ~ (v1_funct_2 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 10.82/11.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 10.82/11.00        | ((sk_E)
% 10.82/11.00            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('simplify', [status(thm)], ['221'])).
% 10.82/11.00  thf('223', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_A)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | ((sk_E)
% 10.82/11.00            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | ~ (v1_funct_1 @ 
% 10.82/11.00             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 10.82/11.00      inference('sup-', [status(thm)], ['110', '222'])).
% 10.82/11.00  thf('224', plain,
% 10.82/11.00      ((~ (v1_funct_1 @ 
% 10.82/11.00           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | ((sk_E)
% 10.82/11.00            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('simplify', [status(thm)], ['223'])).
% 10.82/11.00  thf('225', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_A)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | ((sk_E)
% 10.82/11.00            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 10.82/11.00      inference('sup-', [status(thm)], ['79', '224'])).
% 10.82/11.00  thf('226', plain,
% 10.82/11.00      ((((sk_E)
% 10.82/11.00          = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('simplify', [status(thm)], ['225'])).
% 10.82/11.00  thf('227', plain,
% 10.82/11.00      (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 10.82/11.00          (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('228', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('229', plain,
% 10.82/11.00      (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 10.82/11.00          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 10.82/11.00           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 10.82/11.00           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 10.82/11.00      inference('demod', [status(thm)], ['227', '228'])).
% 10.82/11.00  thf('230', plain,
% 10.82/11.00      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 10.82/11.00           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)
% 10.82/11.00        | (v2_struct_0 @ sk_A)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_D))),
% 10.82/11.00      inference('sup-', [status(thm)], ['226', '229'])).
% 10.82/11.00  thf('231', plain,
% 10.82/11.00      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('sup-', [status(thm)], ['12', '230'])).
% 10.82/11.00  thf(fc2_struct_0, axiom,
% 10.82/11.00    (![A:$i]:
% 10.82/11.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 10.82/11.00       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 10.82/11.00  thf('232', plain,
% 10.82/11.00      (![X7 : $i]:
% 10.82/11.00         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 10.82/11.00          | ~ (l1_struct_0 @ X7)
% 10.82/11.00          | (v2_struct_0 @ X7))),
% 10.82/11.00      inference('cnf', [status(esa)], [fc2_struct_0])).
% 10.82/11.00  thf('233', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | ~ (l1_struct_0 @ sk_B))),
% 10.82/11.00      inference('sup-', [status(thm)], ['231', '232'])).
% 10.82/11.00  thf('234', plain, ((l1_struct_0 @ sk_B)),
% 10.82/11.00      inference('sup-', [status(thm)], ['21', '22'])).
% 10.82/11.00  thf('235', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_B))),
% 10.82/11.00      inference('demod', [status(thm)], ['233', '234'])).
% 10.82/11.00  thf('236', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_D)
% 10.82/11.00        | (v2_struct_0 @ sk_C)
% 10.82/11.00        | (v2_struct_0 @ sk_B)
% 10.82/11.00        | (v2_struct_0 @ sk_A))),
% 10.82/11.00      inference('simplify', [status(thm)], ['235'])).
% 10.82/11.00  thf('237', plain, (~ (v2_struct_0 @ sk_B)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('238', plain,
% 10.82/11.00      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 10.82/11.00      inference('sup-', [status(thm)], ['236', '237'])).
% 10.82/11.00  thf('239', plain, (~ (v2_struct_0 @ sk_A)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('240', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 10.82/11.00      inference('clc', [status(thm)], ['238', '239'])).
% 10.82/11.00  thf('241', plain, (~ (v2_struct_0 @ sk_D)),
% 10.82/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.82/11.00  thf('242', plain, ((v2_struct_0 @ sk_C)),
% 10.82/11.00      inference('clc', [status(thm)], ['240', '241'])).
% 10.82/11.00  thf('243', plain, ($false), inference('demod', [status(thm)], ['0', '242'])).
% 10.82/11.00  
% 10.82/11.00  % SZS output end Refutation
% 10.82/11.00  
% 10.82/11.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
