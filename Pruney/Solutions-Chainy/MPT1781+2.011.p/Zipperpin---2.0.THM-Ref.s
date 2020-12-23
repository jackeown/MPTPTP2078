%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WD4RQubRbu

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:42 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  394 (6055 expanded)
%              Number of leaves         :   39 (1750 expanded)
%              Depth                    :   47
%              Number of atoms          : 5561 (170485 expanded)
%              Number of equality atoms :   69 (2967 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( X7 = X10 )
      | ~ ( r2_funct_2 @ X8 @ X9 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('18',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X32 @ X33 ) @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('26',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','23','31'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('33',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('34',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','51'])).

thf(t59_tmap_1,axiom,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) @ ( u1_struct_0 @ X41 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) @ ( k2_tmap_1 @ X37 @ X39 @ X38 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X37 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['57','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('82',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56','74','79','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','51'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('89',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['57','73'])).

thf('91',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31 ) @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','108'])).

thf('110',plain,
    ( ( sk_C
      = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) @ X43 @ ( k3_tmap_1 @ X45 @ X42 @ X44 @ X44 @ X43 ) )
      | ~ ( m1_pre_topc @ X44 @ X45 )
      | ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( sk_C
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['110','128'])).

thf('130',plain,
    ( sk_C
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['110','128'])).

thf('131',plain,
    ( sk_C
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['110','128'])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','129','130','131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','133'])).

thf('135',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('136',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('138',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X25 )
      | ( ( k3_tmap_1 @ X24 @ X22 @ X25 @ X23 @ X26 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) @ X26 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('147',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('148',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['135','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('153',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('154',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('158',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('159',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['153','160'])).

thf('162',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('163',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('171',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('175',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('176',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['170','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('180',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['169','184'])).

thf('186',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('187',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('191',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('192',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['186','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('196',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( sk_C
      = ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['185','200'])).

thf('202',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('204',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('206',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('207',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,
    ( sk_C
    = ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['201','213'])).

thf('215',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('216',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('217',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( ( k2_tmap_1 @ X20 @ X18 @ X21 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) @ X21 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('220',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['218','219','220','221','222','223','224'])).

thf('226',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['215','225'])).

thf('227',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('228',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['228','229'])).

thf('231',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['151','152','214','232'])).

thf('234',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['235','236'])).

thf('238',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('239',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','237','238','239'])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','241'])).

thf('243',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('246',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('248',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('249',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( m1_subset_1 @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) @ ( k2_tmap_1 @ X37 @ X39 @ X38 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X37 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('257',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['251','252','253','254','255','256','257'])).

thf('259',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['248','258'])).

thf('260',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['235','236'])).

thf('261',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('262',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['259','260','261','262'])).

thf('264',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['247','264'])).

thf('266',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('267',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['265','266'])).

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

thf('268',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('271',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['246','270'])).

thf('272',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['273'])).

thf('275',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('276',plain,(
    ! [X52: $i] :
      ( ~ ( r2_hidden @ X52 @ ( u1_struct_0 @ sk_B ) )
      | ( X52
        = ( k1_funct_1 @ sk_C @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['274','277'])).

thf('279',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['278'])).

thf('280',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['273'])).

thf('281',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['242','243'])).

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

thf('282',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X50 )
      | ~ ( r2_hidden @ X51 @ ( u1_struct_0 @ X49 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X50 @ X49 ) @ X51 )
        = X51 )
      | ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ X50 ) )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('283',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['280','284'])).

thf('286',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['285','286','287','288'])).

thf('290',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['289'])).

thf('291',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('292',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('293',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X4 )
      | ( ( k3_funct_2 @ X4 @ X5 @ X3 @ X6 )
        = ( k1_funct_1 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('294',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['294','295','296'])).

thf('298',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['291','297'])).

thf('299',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ X38 @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) )
       != ( k1_funct_1 @ X40 @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) @ ( k2_tmap_1 @ X37 @ X39 @ X38 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X37 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('300',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('304',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('305',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('306',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['235','236'])).

thf('307',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('311',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('312',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['300','301','302','303','304','305','306','307','308','309','310','311'])).

thf('313',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['312'])).

thf('314',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['290','313'])).

thf('315',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['279','315'])).

thf('317',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['316'])).

thf('318',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['245','317'])).

thf('319',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('320',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['318','319'])).

thf('321',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','23','31'])).

thf('322',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['322','323'])).

thf('325',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( r2_funct_2 @ X8 @ X9 @ X7 @ X10 )
      | ( X7 != X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('327',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_funct_2 @ X8 @ X9 @ X10 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['326'])).

thf('328',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['325','327'])).

thf('329',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['328','329','330'])).

thf('332',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['324','331'])).

thf('333',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['332','333'])).

thf('335',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['334','335'])).

thf('337',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('338',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('339',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['339'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('341',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('342',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['340','341'])).

thf('343',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['336','342'])).

thf('344',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('345',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['343','344'])).

thf('346',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['244','345'])).

thf('347',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['346','347'])).

thf('349',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['348','349'])).

thf('351',plain,
    ( sk_C
    = ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['32','350'])).

thf('352',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['328','329','330'])).

thf('353',plain,(
    $false ),
    inference(demod,[status(thm)],['0','351','352'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WD4RQubRbu
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:20:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.93/2.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.93/2.10  % Solved by: fo/fo7.sh
% 1.93/2.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.10  % done 2472 iterations in 1.637s
% 1.93/2.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.93/2.10  % SZS output start Refutation
% 1.93/2.10  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.93/2.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.93/2.10  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.93/2.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.93/2.10  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.93/2.10  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.93/2.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.93/2.10  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.93/2.10  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 1.93/2.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.93/2.10  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.93/2.10  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 1.93/2.10  thf(sk_B_type, type, sk_B: $i).
% 1.93/2.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.93/2.10  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.93/2.10  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.93/2.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.93/2.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.93/2.10  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.93/2.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.93/2.10  thf(sk_C_type, type, sk_C: $i).
% 1.93/2.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.93/2.10  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.10  thf(t96_tmap_1, conjecture,
% 1.93/2.10    (![A:$i]:
% 1.93/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.10       ( ![B:$i]:
% 1.93/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.10           ( ![C:$i]:
% 1.93/2.10             ( ( ( v1_funct_1 @ C ) & 
% 1.93/2.10                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.93/2.10                 ( m1_subset_1 @
% 1.93/2.10                   C @ 
% 1.93/2.10                   ( k1_zfmisc_1 @
% 1.93/2.10                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.93/2.10               ( ( ![D:$i]:
% 1.93/2.10                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.10                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.93/2.10                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.93/2.10                 ( r2_funct_2 @
% 1.93/2.10                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.93/2.10                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 1.93/2.10  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.10    (~( ![A:$i]:
% 1.93/2.10        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.93/2.10            ( l1_pre_topc @ A ) ) =>
% 1.93/2.10          ( ![B:$i]:
% 1.93/2.10            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.10              ( ![C:$i]:
% 1.93/2.10                ( ( ( v1_funct_1 @ C ) & 
% 1.93/2.10                    ( v1_funct_2 @
% 1.93/2.10                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.93/2.10                    ( m1_subset_1 @
% 1.93/2.10                      C @ 
% 1.93/2.10                      ( k1_zfmisc_1 @
% 1.93/2.10                        ( k2_zfmisc_1 @
% 1.93/2.10                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.93/2.10                  ( ( ![D:$i]:
% 1.93/2.10                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.10                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.93/2.10                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.93/2.10                    ( r2_funct_2 @
% 1.93/2.10                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.93/2.10                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 1.93/2.10    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 1.93/2.10  thf('0', plain,
% 1.93/2.10      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(dt_k4_tmap_1, axiom,
% 1.93/2.10    (![A:$i,B:$i]:
% 1.93/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.93/2.10         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.10       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 1.93/2.10         ( v1_funct_2 @
% 1.93/2.10           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.93/2.10         ( m1_subset_1 @
% 1.93/2.10           ( k4_tmap_1 @ A @ B ) @ 
% 1.93/2.10           ( k1_zfmisc_1 @
% 1.93/2.10             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.93/2.10  thf('2', plain,
% 1.93/2.10      (![X32 : $i, X33 : $i]:
% 1.93/2.10         (~ (l1_pre_topc @ X32)
% 1.93/2.10          | ~ (v2_pre_topc @ X32)
% 1.93/2.10          | (v2_struct_0 @ X32)
% 1.93/2.10          | ~ (m1_pre_topc @ X33 @ X32)
% 1.93/2.10          | (m1_subset_1 @ (k4_tmap_1 @ X32 @ X33) @ 
% 1.93/2.10             (k1_zfmisc_1 @ 
% 1.93/2.10              (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32)))))),
% 1.93/2.10      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.93/2.10  thf('3', plain,
% 1.93/2.10      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10         (k1_zfmisc_1 @ 
% 1.93/2.10          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10        | ~ (l1_pre_topc @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['1', '2'])).
% 1.93/2.10  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('6', plain,
% 1.93/2.10      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10         (k1_zfmisc_1 @ 
% 1.93/2.10          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.93/2.10  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('8', plain,
% 1.93/2.10      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('clc', [status(thm)], ['6', '7'])).
% 1.93/2.10  thf('9', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(redefinition_r2_funct_2, axiom,
% 1.93/2.10    (![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.93/2.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.93/2.10         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.93/2.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.93/2.10       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.93/2.10  thf('10', plain,
% 1.93/2.10      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.93/2.10         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.93/2.10          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 1.93/2.10          | ~ (v1_funct_1 @ X7)
% 1.93/2.10          | ~ (v1_funct_1 @ X10)
% 1.93/2.10          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.93/2.10          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.93/2.10          | ((X7) = (X10))
% 1.93/2.10          | ~ (r2_funct_2 @ X8 @ X9 @ X7 @ X10))),
% 1.93/2.10      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.93/2.10  thf('11', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             X0)
% 1.93/2.10          | ((sk_C) = (X0))
% 1.93/2.10          | ~ (m1_subset_1 @ X0 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ X0)
% 1.93/2.10          | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['9', '10'])).
% 1.93/2.10  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('13', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('14', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             X0)
% 1.93/2.10          | ((sk_C) = (X0))
% 1.93/2.10          | ~ (m1_subset_1 @ X0 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ X0))),
% 1.93/2.10      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.93/2.10  thf('15', plain,
% 1.93/2.10      ((~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10             (u1_struct_0 @ sk_A))
% 1.93/2.10        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['8', '14'])).
% 1.93/2.10  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('17', plain,
% 1.93/2.10      (![X32 : $i, X33 : $i]:
% 1.93/2.10         (~ (l1_pre_topc @ X32)
% 1.93/2.10          | ~ (v2_pre_topc @ X32)
% 1.93/2.10          | (v2_struct_0 @ X32)
% 1.93/2.10          | ~ (m1_pre_topc @ X33 @ X32)
% 1.93/2.10          | (v1_funct_1 @ (k4_tmap_1 @ X32 @ X33)))),
% 1.93/2.10      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.93/2.10  thf('18', plain,
% 1.93/2.10      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10        | ~ (l1_pre_topc @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['16', '17'])).
% 1.93/2.10  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('21', plain,
% 1.93/2.10      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.93/2.10  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('23', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.93/2.10      inference('clc', [status(thm)], ['21', '22'])).
% 1.93/2.10  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('25', plain,
% 1.93/2.10      (![X32 : $i, X33 : $i]:
% 1.93/2.10         (~ (l1_pre_topc @ X32)
% 1.93/2.10          | ~ (v2_pre_topc @ X32)
% 1.93/2.10          | (v2_struct_0 @ X32)
% 1.93/2.10          | ~ (m1_pre_topc @ X33 @ X32)
% 1.93/2.10          | (v1_funct_2 @ (k4_tmap_1 @ X32 @ X33) @ (u1_struct_0 @ X33) @ 
% 1.93/2.10             (u1_struct_0 @ X32)))),
% 1.93/2.10      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.93/2.10  thf('26', plain,
% 1.93/2.10      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10         (u1_struct_0 @ sk_A))
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10        | ~ (l1_pre_topc @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['24', '25'])).
% 1.93/2.10  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('29', plain,
% 1.93/2.10      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10         (u1_struct_0 @ sk_A))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.93/2.10  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('31', plain,
% 1.93/2.10      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10        (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('clc', [status(thm)], ['29', '30'])).
% 1.93/2.10  thf('32', plain,
% 1.93/2.10      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.93/2.10      inference('demod', [status(thm)], ['15', '23', '31'])).
% 1.93/2.10  thf(t2_tsep_1, axiom,
% 1.93/2.10    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.93/2.10  thf('33', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('34', plain,
% 1.93/2.10      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('clc', [status(thm)], ['6', '7'])).
% 1.93/2.10  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('37', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(dt_k3_tmap_1, axiom,
% 1.93/2.10    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.93/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.93/2.10         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.93/2.10         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.93/2.10         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.93/2.10         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.93/2.10         ( m1_subset_1 @
% 1.93/2.10           E @ 
% 1.93/2.10           ( k1_zfmisc_1 @
% 1.93/2.10             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.93/2.10       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.93/2.10         ( v1_funct_2 @
% 1.93/2.10           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.93/2.10           ( u1_struct_0 @ B ) ) & 
% 1.93/2.10         ( m1_subset_1 @
% 1.93/2.10           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.93/2.10           ( k1_zfmisc_1 @
% 1.93/2.10             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.93/2.10  thf('38', plain,
% 1.93/2.10      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X27 @ X28)
% 1.93/2.10          | ~ (m1_pre_topc @ X29 @ X28)
% 1.93/2.10          | ~ (l1_pre_topc @ X30)
% 1.93/2.10          | ~ (v2_pre_topc @ X30)
% 1.93/2.10          | (v2_struct_0 @ X30)
% 1.93/2.10          | ~ (l1_pre_topc @ X28)
% 1.93/2.10          | ~ (v2_pre_topc @ X28)
% 1.93/2.10          | (v2_struct_0 @ X28)
% 1.93/2.10          | ~ (v1_funct_1 @ X31)
% 1.93/2.10          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 1.93/2.10          | ~ (m1_subset_1 @ X31 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 1.93/2.10          | (m1_subset_1 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31) @ 
% 1.93/2.10             (k1_zfmisc_1 @ 
% 1.93/2.10              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X30)))))),
% 1.93/2.10      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.93/2.10  thf('39', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10           (k1_zfmisc_1 @ 
% 1.93/2.10            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10          | (v2_struct_0 @ X1)
% 1.93/2.10          | ~ (v2_pre_topc @ X1)
% 1.93/2.10          | ~ (l1_pre_topc @ X1)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.93/2.10      inference('sup-', [status(thm)], ['37', '38'])).
% 1.93/2.10  thf('40', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('44', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10           (k1_zfmisc_1 @ 
% 1.93/2.10            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | (v2_struct_0 @ X1)
% 1.93/2.10          | ~ (v2_pre_topc @ X1)
% 1.93/2.10          | ~ (l1_pre_topc @ X1)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.93/2.10      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 1.93/2.10  thf('45', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (k1_zfmisc_1 @ 
% 1.93/2.10              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.93/2.10      inference('sup-', [status(thm)], ['36', '44'])).
% 1.93/2.10  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('48', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (k1_zfmisc_1 @ 
% 1.93/2.10              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.93/2.10      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.93/2.10  thf('49', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10           (k1_zfmisc_1 @ 
% 1.93/2.10            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['48'])).
% 1.93/2.10  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('51', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.10          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (k1_zfmisc_1 @ 
% 1.93/2.10              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.93/2.10      inference('clc', [status(thm)], ['49', '50'])).
% 1.93/2.10  thf('52', plain,
% 1.93/2.10      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('sup-', [status(thm)], ['35', '51'])).
% 1.93/2.10  thf(t59_tmap_1, axiom,
% 1.93/2.10    (![A:$i]:
% 1.93/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.10       ( ![B:$i]:
% 1.93/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.93/2.10             ( l1_pre_topc @ B ) ) =>
% 1.93/2.10           ( ![C:$i]:
% 1.93/2.10             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 1.93/2.10               ( ![D:$i]:
% 1.93/2.10                 ( ( ( v1_funct_1 @ D ) & 
% 1.93/2.10                     ( v1_funct_2 @
% 1.93/2.10                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.93/2.10                     ( m1_subset_1 @
% 1.93/2.10                       D @ 
% 1.93/2.10                       ( k1_zfmisc_1 @
% 1.93/2.10                         ( k2_zfmisc_1 @
% 1.93/2.10                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.93/2.10                   ( ![E:$i]:
% 1.93/2.10                     ( ( ( v1_funct_1 @ E ) & 
% 1.93/2.10                         ( v1_funct_2 @
% 1.93/2.10                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 1.93/2.10                         ( m1_subset_1 @
% 1.93/2.10                           E @ 
% 1.93/2.10                           ( k1_zfmisc_1 @
% 1.93/2.10                             ( k2_zfmisc_1 @
% 1.93/2.10                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.93/2.10                       ( ( ![F:$i]:
% 1.93/2.10                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 1.93/2.10                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 1.93/2.10                               ( ( k3_funct_2 @
% 1.93/2.10                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.93/2.10                                   D @ F ) =
% 1.93/2.10                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 1.93/2.10                         ( r2_funct_2 @
% 1.93/2.10                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 1.93/2.10                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 1.93/2.10  thf('53', plain,
% 1.93/2.10      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X37)
% 1.93/2.10          | ~ (v2_pre_topc @ X37)
% 1.93/2.10          | ~ (l1_pre_topc @ X37)
% 1.93/2.10          | ~ (v1_funct_1 @ X38)
% 1.93/2.10          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 1.93/2.10          | ~ (m1_subset_1 @ X38 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 1.93/2.10          | (r2_hidden @ (sk_F @ X40 @ X38 @ X41 @ X37 @ X39) @ 
% 1.93/2.10             (u1_struct_0 @ X41))
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39) @ 
% 1.93/2.10             (k2_tmap_1 @ X37 @ X39 @ X38 @ X41) @ X40)
% 1.93/2.10          | ~ (m1_subset_1 @ X40 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 1.93/2.10          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 1.93/2.10          | ~ (v1_funct_1 @ X40)
% 1.93/2.10          | ~ (m1_pre_topc @ X41 @ X37)
% 1.93/2.10          | (v2_struct_0 @ X41)
% 1.93/2.10          | ~ (l1_pre_topc @ X39)
% 1.93/2.10          | ~ (v2_pre_topc @ X39)
% 1.93/2.10          | (v2_struct_0 @ X39))),
% 1.93/2.10      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.93/2.10  thf('54', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ X0)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ~ (v1_funct_1 @ X1)
% 1.93/2.10          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (m1_subset_1 @ X1 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10             (k2_tmap_1 @ sk_B @ sk_A @ 
% 1.93/2.10              (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ X0) @ 
% 1.93/2.10             X1)
% 1.93/2.10          | (r2_hidden @ 
% 1.93/2.10             (sk_F @ X1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10              X0 @ sk_B @ sk_A) @ 
% 1.93/2.10             (u1_struct_0 @ X0))
% 1.93/2.10          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10          | ~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['52', '53'])).
% 1.93/2.10  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('58', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('59', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('60', plain,
% 1.93/2.10      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X27 @ X28)
% 1.93/2.10          | ~ (m1_pre_topc @ X29 @ X28)
% 1.93/2.10          | ~ (l1_pre_topc @ X30)
% 1.93/2.10          | ~ (v2_pre_topc @ X30)
% 1.93/2.10          | (v2_struct_0 @ X30)
% 1.93/2.10          | ~ (l1_pre_topc @ X28)
% 1.93/2.10          | ~ (v2_pre_topc @ X28)
% 1.93/2.10          | (v2_struct_0 @ X28)
% 1.93/2.10          | ~ (v1_funct_1 @ X31)
% 1.93/2.10          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 1.93/2.10          | ~ (m1_subset_1 @ X31 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 1.93/2.10          | (v1_funct_1 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31)))),
% 1.93/2.10      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.93/2.10  thf('61', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 1.93/2.10          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10          | (v2_struct_0 @ X1)
% 1.93/2.10          | ~ (v2_pre_topc @ X1)
% 1.93/2.10          | ~ (l1_pre_topc @ X1)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.93/2.10      inference('sup-', [status(thm)], ['59', '60'])).
% 1.93/2.10  thf('62', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('66', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 1.93/2.10          | (v2_struct_0 @ X1)
% 1.93/2.10          | ~ (v2_pre_topc @ X1)
% 1.93/2.10          | ~ (l1_pre_topc @ X1)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.93/2.10      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 1.93/2.10  thf('67', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['58', '66'])).
% 1.93/2.10  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('70', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)))),
% 1.93/2.10      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.93/2.10  thf('71', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C))
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['70'])).
% 1.93/2.10  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('73', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.10          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)))),
% 1.93/2.10      inference('clc', [status(thm)], ['71', '72'])).
% 1.93/2.10  thf('74', plain,
% 1.93/2.10      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.93/2.10      inference('sup-', [status(thm)], ['57', '73'])).
% 1.93/2.10  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(dt_m1_pre_topc, axiom,
% 1.93/2.10    (![A:$i]:
% 1.93/2.10     ( ( l1_pre_topc @ A ) =>
% 1.93/2.10       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.93/2.10  thf('76', plain,
% 1.93/2.10      (![X13 : $i, X14 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X13 @ X14)
% 1.93/2.10          | (l1_pre_topc @ X13)
% 1.93/2.10          | ~ (l1_pre_topc @ X14))),
% 1.93/2.10      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.93/2.10  thf('77', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['75', '76'])).
% 1.93/2.10  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('80', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(cc1_pre_topc, axiom,
% 1.93/2.10    (![A:$i]:
% 1.93/2.10     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.10       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.93/2.10  thf('81', plain,
% 1.93/2.10      (![X11 : $i, X12 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X11 @ X12)
% 1.93/2.10          | (v2_pre_topc @ X11)
% 1.93/2.10          | ~ (l1_pre_topc @ X12)
% 1.93/2.10          | ~ (v2_pre_topc @ X12))),
% 1.93/2.10      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.93/2.10  thf('82', plain,
% 1.93/2.10      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['80', '81'])).
% 1.93/2.10  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('85', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.93/2.10  thf('86', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ X0)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ~ (v1_funct_1 @ X1)
% 1.93/2.10          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (m1_subset_1 @ X1 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10             (k2_tmap_1 @ sk_B @ sk_A @ 
% 1.93/2.10              (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ X0) @ 
% 1.93/2.10             X1)
% 1.93/2.10          | (r2_hidden @ 
% 1.93/2.10             (sk_F @ X1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10              X0 @ sk_B @ sk_A) @ 
% 1.93/2.10             (u1_struct_0 @ X0))
% 1.93/2.10          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('demod', [status(thm)], ['54', '55', '56', '74', '79', '85'])).
% 1.93/2.10  thf('87', plain,
% 1.93/2.10      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('sup-', [status(thm)], ['35', '51'])).
% 1.93/2.10  thf('88', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             X0)
% 1.93/2.10          | ((sk_C) = (X0))
% 1.93/2.10          | ~ (m1_subset_1 @ X0 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ X0))),
% 1.93/2.10      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.93/2.10  thf('89', plain,
% 1.93/2.10      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10        | ((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['87', '88'])).
% 1.93/2.10  thf('90', plain,
% 1.93/2.10      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.93/2.10      inference('sup-', [status(thm)], ['57', '73'])).
% 1.93/2.10  thf('91', plain,
% 1.93/2.10      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10        | ((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.93/2.10      inference('demod', [status(thm)], ['89', '90'])).
% 1.93/2.10  thf('92', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('93', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('94', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('95', plain,
% 1.93/2.10      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X27 @ X28)
% 1.93/2.10          | ~ (m1_pre_topc @ X29 @ X28)
% 1.93/2.10          | ~ (l1_pre_topc @ X30)
% 1.93/2.10          | ~ (v2_pre_topc @ X30)
% 1.93/2.10          | (v2_struct_0 @ X30)
% 1.93/2.10          | ~ (l1_pre_topc @ X28)
% 1.93/2.10          | ~ (v2_pre_topc @ X28)
% 1.93/2.10          | (v2_struct_0 @ X28)
% 1.93/2.10          | ~ (v1_funct_1 @ X31)
% 1.93/2.10          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 1.93/2.10          | ~ (m1_subset_1 @ X31 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 1.93/2.10          | (v1_funct_2 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31) @ 
% 1.93/2.10             (u1_struct_0 @ X27) @ (u1_struct_0 @ X30)))),
% 1.93/2.10      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.93/2.10  thf('96', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10          | (v2_struct_0 @ X1)
% 1.93/2.10          | ~ (v2_pre_topc @ X1)
% 1.93/2.10          | ~ (l1_pre_topc @ X1)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.93/2.10      inference('sup-', [status(thm)], ['94', '95'])).
% 1.93/2.10  thf('97', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('101', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | (v2_struct_0 @ X1)
% 1.93/2.10          | ~ (v2_pre_topc @ X1)
% 1.93/2.10          | ~ (l1_pre_topc @ X1)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.93/2.10      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 1.93/2.10  thf('102', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['93', '101'])).
% 1.93/2.10  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('105', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.93/2.10  thf('106', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['105'])).
% 1.93/2.10  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('108', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.10          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('clc', [status(thm)], ['106', '107'])).
% 1.93/2.10  thf('109', plain,
% 1.93/2.10      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['92', '108'])).
% 1.93/2.10  thf('110', plain,
% 1.93/2.10      ((((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.93/2.10      inference('demod', [status(thm)], ['91', '109'])).
% 1.93/2.10  thf('111', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('112', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(t74_tmap_1, axiom,
% 1.93/2.10    (![A:$i]:
% 1.93/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.10       ( ![B:$i]:
% 1.93/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.93/2.10             ( l1_pre_topc @ B ) ) =>
% 1.93/2.10           ( ![C:$i]:
% 1.93/2.10             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.10               ( ![D:$i]:
% 1.93/2.10                 ( ( ( v1_funct_1 @ D ) & 
% 1.93/2.10                     ( v1_funct_2 @
% 1.93/2.10                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.93/2.10                     ( m1_subset_1 @
% 1.93/2.10                       D @ 
% 1.93/2.10                       ( k1_zfmisc_1 @
% 1.93/2.10                         ( k2_zfmisc_1 @
% 1.93/2.10                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.93/2.10                   ( r2_funct_2 @
% 1.93/2.10                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 1.93/2.10                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 1.93/2.10  thf('113', plain,
% 1.93/2.10      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X42)
% 1.93/2.10          | ~ (v2_pre_topc @ X42)
% 1.93/2.10          | ~ (l1_pre_topc @ X42)
% 1.93/2.10          | ~ (v1_funct_1 @ X43)
% 1.93/2.10          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 1.93/2.10          | ~ (m1_subset_1 @ X43 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42) @ X43 @ 
% 1.93/2.10             (k3_tmap_1 @ X45 @ X42 @ X44 @ X44 @ X43))
% 1.93/2.10          | ~ (m1_pre_topc @ X44 @ X45)
% 1.93/2.10          | (v2_struct_0 @ X44)
% 1.93/2.10          | ~ (l1_pre_topc @ X45)
% 1.93/2.10          | ~ (v2_pre_topc @ X45)
% 1.93/2.10          | (v2_struct_0 @ X45))),
% 1.93/2.10      inference('cnf', [status(esa)], [t74_tmap_1])).
% 1.93/2.10  thf('114', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X0)
% 1.93/2.10          | ~ (v2_pre_topc @ X0)
% 1.93/2.10          | ~ (l1_pre_topc @ X0)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['112', '113'])).
% 1.93/2.10  thf('115', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('119', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X0)
% 1.93/2.10          | ~ (v2_pre_topc @ X0)
% 1.93/2.10          | ~ (l1_pre_topc @ X0)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 1.93/2.10  thf('120', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['111', '119'])).
% 1.93/2.10  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('123', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.93/2.10  thf('124', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['123'])).
% 1.93/2.10  thf('125', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('126', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.93/2.10      inference('clc', [status(thm)], ['124', '125'])).
% 1.93/2.10  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('128', plain,
% 1.93/2.10      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10        (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.93/2.10      inference('clc', [status(thm)], ['126', '127'])).
% 1.93/2.10  thf('129', plain,
% 1.93/2.10      (((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.93/2.10      inference('demod', [status(thm)], ['110', '128'])).
% 1.93/2.10  thf('130', plain,
% 1.93/2.10      (((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.93/2.10      inference('demod', [status(thm)], ['110', '128'])).
% 1.93/2.10  thf('131', plain,
% 1.93/2.10      (((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.93/2.10      inference('demod', [status(thm)], ['110', '128'])).
% 1.93/2.10  thf('132', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('133', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ X0)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ~ (v1_funct_1 @ X1)
% 1.93/2.10          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (m1_subset_1 @ X1 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.93/2.10          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.93/2.10             (u1_struct_0 @ X0))
% 1.93/2.10          | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('demod', [status(thm)], ['86', '129', '130', '131', '132'])).
% 1.93/2.10  thf('134', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_hidden @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10             (u1_struct_0 @ sk_A))
% 1.93/2.10        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['34', '133'])).
% 1.93/2.10  thf('135', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('136', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('137', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(d5_tmap_1, axiom,
% 1.93/2.10    (![A:$i]:
% 1.93/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.10       ( ![B:$i]:
% 1.93/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.93/2.10             ( l1_pre_topc @ B ) ) =>
% 1.93/2.10           ( ![C:$i]:
% 1.93/2.10             ( ( m1_pre_topc @ C @ A ) =>
% 1.93/2.10               ( ![D:$i]:
% 1.93/2.10                 ( ( m1_pre_topc @ D @ A ) =>
% 1.93/2.10                   ( ![E:$i]:
% 1.93/2.10                     ( ( ( v1_funct_1 @ E ) & 
% 1.93/2.10                         ( v1_funct_2 @
% 1.93/2.10                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.93/2.10                         ( m1_subset_1 @
% 1.93/2.10                           E @ 
% 1.93/2.10                           ( k1_zfmisc_1 @
% 1.93/2.10                             ( k2_zfmisc_1 @
% 1.93/2.10                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.93/2.10                       ( ( m1_pre_topc @ D @ C ) =>
% 1.93/2.10                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.93/2.10                           ( k2_partfun1 @
% 1.93/2.10                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.93/2.10                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.93/2.10  thf('138', plain,
% 1.93/2.10      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X22)
% 1.93/2.10          | ~ (v2_pre_topc @ X22)
% 1.93/2.10          | ~ (l1_pre_topc @ X22)
% 1.93/2.10          | ~ (m1_pre_topc @ X23 @ X24)
% 1.93/2.10          | ~ (m1_pre_topc @ X23 @ X25)
% 1.93/2.10          | ((k3_tmap_1 @ X24 @ X22 @ X25 @ X23 @ X26)
% 1.93/2.10              = (k2_partfun1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22) @ 
% 1.93/2.10                 X26 @ (u1_struct_0 @ X23)))
% 1.93/2.10          | ~ (m1_subset_1 @ X26 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))))
% 1.93/2.10          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))
% 1.93/2.10          | ~ (v1_funct_1 @ X26)
% 1.93/2.10          | ~ (m1_pre_topc @ X25 @ X24)
% 1.93/2.10          | ~ (l1_pre_topc @ X24)
% 1.93/2.10          | ~ (v2_pre_topc @ X24)
% 1.93/2.10          | (v2_struct_0 @ X24))),
% 1.93/2.10      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.93/2.10  thf('139', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X0)
% 1.93/2.10          | ~ (v2_pre_topc @ X0)
% 1.93/2.10          | ~ (l1_pre_topc @ X0)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.10          | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 1.93/2.10              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10                 sk_C @ (u1_struct_0 @ X1)))
% 1.93/2.10          | ~ (m1_pre_topc @ X1 @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ X1 @ X0)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['137', '138'])).
% 1.93/2.10  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('141', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('144', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X0)
% 1.93/2.10          | ~ (v2_pre_topc @ X0)
% 1.93/2.10          | ~ (l1_pre_topc @ X0)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.10          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 1.93/2.10              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10                 sk_C @ (u1_struct_0 @ X1)))
% 1.93/2.10          | ~ (m1_pre_topc @ X1 @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ X1 @ X0)
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 1.93/2.10  thf('145', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 1.93/2.10              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10                 sk_C @ (u1_struct_0 @ X0)))
% 1.93/2.10          | ~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['136', '144'])).
% 1.93/2.10  thf('146', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('147', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('148', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.93/2.10  thf('149', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 1.93/2.10              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10                 sk_C @ (u1_struct_0 @ X0)))
% 1.93/2.10          | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 1.93/2.10  thf('150', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_B)
% 1.93/2.10          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 1.93/2.10              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10                 sk_C @ (u1_struct_0 @ X0)))
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['149'])).
% 1.93/2.10  thf('151', plain,
% 1.93/2.10      ((~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 1.93/2.10            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10               sk_C @ (u1_struct_0 @ sk_B)))
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['135', '150'])).
% 1.93/2.10  thf('152', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('153', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('154', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('155', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10           (k1_zfmisc_1 @ 
% 1.93/2.10            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | (v2_struct_0 @ X1)
% 1.93/2.10          | ~ (v2_pre_topc @ X1)
% 1.93/2.10          | ~ (l1_pre_topc @ X1)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.93/2.10      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 1.93/2.10  thf('156', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (k1_zfmisc_1 @ 
% 1.93/2.10              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.93/2.10      inference('sup-', [status(thm)], ['154', '155'])).
% 1.93/2.10  thf('157', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('158', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('159', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.93/2.10  thf('160', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (k1_zfmisc_1 @ 
% 1.93/2.10              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.93/2.10      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 1.93/2.10  thf('161', plain,
% 1.93/2.10      ((~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | (m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10           (k1_zfmisc_1 @ 
% 1.93/2.10            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['153', '160'])).
% 1.93/2.10  thf('162', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('163', plain,
% 1.93/2.10      (((m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10         (k1_zfmisc_1 @ 
% 1.93/2.10          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['161', '162'])).
% 1.93/2.10  thf('164', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('165', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10           (k1_zfmisc_1 @ 
% 1.93/2.10            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 1.93/2.10      inference('clc', [status(thm)], ['163', '164'])).
% 1.93/2.10  thf('166', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('167', plain,
% 1.93/2.10      ((m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('clc', [status(thm)], ['165', '166'])).
% 1.93/2.10  thf('168', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             X0)
% 1.93/2.10          | ((sk_C) = (X0))
% 1.93/2.10          | ~ (m1_subset_1 @ X0 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ X0))),
% 1.93/2.10      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.93/2.10  thf('169', plain,
% 1.93/2.10      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10        | ((sk_C) = (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['167', '168'])).
% 1.93/2.10  thf('170', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('171', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('172', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 1.93/2.10          | (v2_struct_0 @ X1)
% 1.93/2.10          | ~ (v2_pre_topc @ X1)
% 1.93/2.10          | ~ (l1_pre_topc @ X1)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.93/2.10      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 1.93/2.10  thf('173', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['171', '172'])).
% 1.93/2.10  thf('174', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('175', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('176', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.93/2.10  thf('177', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)))),
% 1.93/2.10      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 1.93/2.10  thf('178', plain,
% 1.93/2.10      ((~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['170', '177'])).
% 1.93/2.10  thf('179', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('180', plain,
% 1.93/2.10      (((v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['178', '179'])).
% 1.93/2.10  thf('181', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('182', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.93/2.10      inference('clc', [status(thm)], ['180', '181'])).
% 1.93/2.10  thf('183', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('184', plain,
% 1.93/2.10      ((v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.93/2.10      inference('clc', [status(thm)], ['182', '183'])).
% 1.93/2.10  thf('185', plain,
% 1.93/2.10      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10        | ((sk_C) = (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.93/2.10      inference('demod', [status(thm)], ['169', '184'])).
% 1.93/2.10  thf('186', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('187', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('188', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | (v2_struct_0 @ X1)
% 1.93/2.10          | ~ (v2_pre_topc @ X1)
% 1.93/2.10          | ~ (l1_pre_topc @ X1)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.93/2.10      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 1.93/2.10  thf('189', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['187', '188'])).
% 1.93/2.10  thf('190', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('191', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('192', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.93/2.10  thf('193', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.93/2.10             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 1.93/2.10  thf('194', plain,
% 1.93/2.10      ((~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['186', '193'])).
% 1.93/2.10  thf('195', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('196', plain,
% 1.93/2.10      (((v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['194', '195'])).
% 1.93/2.10  thf('197', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('198', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('clc', [status(thm)], ['196', '197'])).
% 1.93/2.10  thf('199', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('200', plain,
% 1.93/2.10      ((v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.93/2.10        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('clc', [status(thm)], ['198', '199'])).
% 1.93/2.10  thf('201', plain,
% 1.93/2.10      ((((sk_C) = (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.93/2.10      inference('demod', [status(thm)], ['185', '200'])).
% 1.93/2.10  thf('202', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('203', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X0)
% 1.93/2.10          | ~ (v2_pre_topc @ X0)
% 1.93/2.10          | ~ (l1_pre_topc @ X0)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 1.93/2.10  thf('204', plain,
% 1.93/2.10      ((~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | ~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | ~ (v2_pre_topc @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['202', '203'])).
% 1.93/2.10  thf('205', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('206', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('207', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.93/2.10  thf('208', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 1.93/2.10  thf('209', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['208'])).
% 1.93/2.10  thf('210', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('211', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.93/2.10      inference('clc', [status(thm)], ['209', '210'])).
% 1.93/2.10  thf('212', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('213', plain,
% 1.93/2.10      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10        (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.93/2.10      inference('clc', [status(thm)], ['211', '212'])).
% 1.93/2.10  thf('214', plain,
% 1.93/2.10      (((sk_C) = (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.93/2.10      inference('demod', [status(thm)], ['201', '213'])).
% 1.93/2.10  thf('215', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('216', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(d4_tmap_1, axiom,
% 1.93/2.10    (![A:$i]:
% 1.93/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.10       ( ![B:$i]:
% 1.93/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.93/2.10             ( l1_pre_topc @ B ) ) =>
% 1.93/2.10           ( ![C:$i]:
% 1.93/2.10             ( ( ( v1_funct_1 @ C ) & 
% 1.93/2.10                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.93/2.10                 ( m1_subset_1 @
% 1.93/2.10                   C @ 
% 1.93/2.10                   ( k1_zfmisc_1 @
% 1.93/2.10                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.93/2.10               ( ![D:$i]:
% 1.93/2.10                 ( ( m1_pre_topc @ D @ A ) =>
% 1.93/2.10                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.93/2.10                     ( k2_partfun1 @
% 1.93/2.10                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.93/2.10                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.93/2.10  thf('217', plain,
% 1.93/2.10      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X18)
% 1.93/2.10          | ~ (v2_pre_topc @ X18)
% 1.93/2.10          | ~ (l1_pre_topc @ X18)
% 1.93/2.10          | ~ (m1_pre_topc @ X19 @ X20)
% 1.93/2.10          | ((k2_tmap_1 @ X20 @ X18 @ X21 @ X19)
% 1.93/2.10              = (k2_partfun1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18) @ 
% 1.93/2.10                 X21 @ (u1_struct_0 @ X19)))
% 1.93/2.10          | ~ (m1_subset_1 @ X21 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 1.93/2.10          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 1.93/2.10          | ~ (v1_funct_1 @ X21)
% 1.93/2.10          | ~ (l1_pre_topc @ X20)
% 1.93/2.10          | ~ (v2_pre_topc @ X20)
% 1.93/2.10          | (v2_struct_0 @ X20))),
% 1.93/2.10      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.93/2.10  thf('218', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_B)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_B)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 1.93/2.10              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10                 sk_C @ (u1_struct_0 @ X0)))
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['216', '217'])).
% 1.93/2.10  thf('219', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.93/2.10  thf('220', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('222', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('223', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('224', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('225', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_B)
% 1.93/2.10          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 1.93/2.10              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10                 sk_C @ (u1_struct_0 @ X0)))
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)],
% 1.93/2.10                ['218', '219', '220', '221', '222', '223', '224'])).
% 1.93/2.10  thf('226', plain,
% 1.93/2.10      ((~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 1.93/2.10            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10               sk_C @ (u1_struct_0 @ sk_B)))
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['215', '225'])).
% 1.93/2.10  thf('227', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('228', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 1.93/2.10            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10               sk_C @ (u1_struct_0 @ sk_B)))
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('demod', [status(thm)], ['226', '227'])).
% 1.93/2.10  thf('229', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('230', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 1.93/2.10            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10               sk_C @ (u1_struct_0 @ sk_B))))),
% 1.93/2.10      inference('clc', [status(thm)], ['228', '229'])).
% 1.93/2.10  thf('231', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('232', plain,
% 1.93/2.10      (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 1.93/2.10         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10            (u1_struct_0 @ sk_B)))),
% 1.93/2.10      inference('clc', [status(thm)], ['230', '231'])).
% 1.93/2.10  thf('233', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | ((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('demod', [status(thm)], ['151', '152', '214', '232'])).
% 1.93/2.10  thf('234', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('235', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | ((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.93/2.10      inference('clc', [status(thm)], ['233', '234'])).
% 1.93/2.10  thf('236', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('237', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 1.93/2.10      inference('clc', [status(thm)], ['235', '236'])).
% 1.93/2.10  thf('238', plain,
% 1.93/2.10      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10        (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('clc', [status(thm)], ['29', '30'])).
% 1.93/2.10  thf('239', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.93/2.10      inference('clc', [status(thm)], ['21', '22'])).
% 1.93/2.10  thf('240', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_hidden @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['134', '237', '238', '239'])).
% 1.93/2.10  thf('241', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (r2_hidden @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('simplify', [status(thm)], ['240'])).
% 1.93/2.10  thf('242', plain,
% 1.93/2.10      ((~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_hidden @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['33', '241'])).
% 1.93/2.10  thf('243', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('244', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_hidden @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['242', '243'])).
% 1.93/2.10  thf('245', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('246', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('247', plain,
% 1.93/2.10      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.10      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.10  thf('248', plain,
% 1.93/2.10      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('clc', [status(thm)], ['6', '7'])).
% 1.93/2.10  thf('249', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('250', plain,
% 1.93/2.10      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X37)
% 1.93/2.10          | ~ (v2_pre_topc @ X37)
% 1.93/2.10          | ~ (l1_pre_topc @ X37)
% 1.93/2.10          | ~ (v1_funct_1 @ X38)
% 1.93/2.10          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 1.93/2.10          | ~ (m1_subset_1 @ X38 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 1.93/2.10          | (m1_subset_1 @ (sk_F @ X40 @ X38 @ X41 @ X37 @ X39) @ 
% 1.93/2.10             (u1_struct_0 @ X37))
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39) @ 
% 1.93/2.10             (k2_tmap_1 @ X37 @ X39 @ X38 @ X41) @ X40)
% 1.93/2.10          | ~ (m1_subset_1 @ X40 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 1.93/2.10          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 1.93/2.10          | ~ (v1_funct_1 @ X40)
% 1.93/2.10          | ~ (m1_pre_topc @ X41 @ X37)
% 1.93/2.10          | (v2_struct_0 @ X41)
% 1.93/2.10          | ~ (l1_pre_topc @ X39)
% 1.93/2.10          | ~ (v2_pre_topc @ X39)
% 1.93/2.10          | (v2_struct_0 @ X39))),
% 1.93/2.10      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.93/2.10  thf('251', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_A)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ X0)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ~ (v1_funct_1 @ X1)
% 1.93/2.10          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (m1_subset_1 @ X1 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.93/2.10          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.93/2.10             (u1_struct_0 @ sk_B))
% 1.93/2.10          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10          | ~ (l1_pre_topc @ sk_B)
% 1.93/2.10          | ~ (v2_pre_topc @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['249', '250'])).
% 1.93/2.10  thf('252', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('253', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('254', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('255', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('256', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('257', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.93/2.10  thf('258', plain,
% 1.93/2.10      (![X0 : $i, X1 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_A)
% 1.93/2.10          | (v2_struct_0 @ X0)
% 1.93/2.10          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.93/2.10          | ~ (v1_funct_1 @ X1)
% 1.93/2.10          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.93/2.10          | ~ (m1_subset_1 @ X1 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.93/2.10          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.93/2.10             (u1_struct_0 @ sk_B))
% 1.93/2.10          | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('demod', [status(thm)],
% 1.93/2.10                ['251', '252', '253', '254', '255', '256', '257'])).
% 1.93/2.10  thf('259', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (m1_subset_1 @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10             (u1_struct_0 @ sk_A))
% 1.93/2.10        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['248', '258'])).
% 1.93/2.10  thf('260', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 1.93/2.10      inference('clc', [status(thm)], ['235', '236'])).
% 1.93/2.10  thf('261', plain,
% 1.93/2.10      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10        (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('clc', [status(thm)], ['29', '30'])).
% 1.93/2.10  thf('262', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.93/2.10      inference('clc', [status(thm)], ['21', '22'])).
% 1.93/2.10  thf('263', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (m1_subset_1 @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['259', '260', '261', '262'])).
% 1.93/2.10  thf('264', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (m1_subset_1 @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('simplify', [status(thm)], ['263'])).
% 1.93/2.10  thf('265', plain,
% 1.93/2.10      ((~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (m1_subset_1 @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['247', '264'])).
% 1.93/2.10  thf('266', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('267', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (m1_subset_1 @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['265', '266'])).
% 1.93/2.10  thf(t55_pre_topc, axiom,
% 1.93/2.10    (![A:$i]:
% 1.93/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.10       ( ![B:$i]:
% 1.93/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.10           ( ![C:$i]:
% 1.93/2.10             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.93/2.10               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.93/2.10  thf('268', plain,
% 1.93/2.10      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X15)
% 1.93/2.10          | ~ (m1_pre_topc @ X15 @ X16)
% 1.93/2.10          | (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 1.93/2.10          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 1.93/2.10          | ~ (l1_pre_topc @ X16)
% 1.93/2.10          | (v2_struct_0 @ X16))),
% 1.93/2.10      inference('cnf', [status(esa)], [t55_pre_topc])).
% 1.93/2.10  thf('269', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_A)
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ X0)
% 1.93/2.10          | ~ (l1_pre_topc @ X0)
% 1.93/2.10          | (m1_subset_1 @ 
% 1.93/2.10             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10             (u1_struct_0 @ X0))
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.10          | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['267', '268'])).
% 1.93/2.10  thf('270', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.10          | (m1_subset_1 @ 
% 1.93/2.10             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10             (u1_struct_0 @ X0))
% 1.93/2.10          | ~ (l1_pre_topc @ X0)
% 1.93/2.10          | (v2_struct_0 @ X0)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['269'])).
% 1.93/2.10  thf('271', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10        | (m1_subset_1 @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['246', '270'])).
% 1.93/2.10  thf('272', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('273', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (m1_subset_1 @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('demod', [status(thm)], ['271', '272'])).
% 1.93/2.10  thf('274', plain,
% 1.93/2.10      (((m1_subset_1 @ 
% 1.93/2.10         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10         (u1_struct_0 @ sk_A))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['273'])).
% 1.93/2.10  thf('275', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_hidden @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['242', '243'])).
% 1.93/2.10  thf('276', plain,
% 1.93/2.10      (![X52 : $i]:
% 1.93/2.10         (~ (r2_hidden @ X52 @ (u1_struct_0 @ sk_B))
% 1.93/2.10          | ((X52) = (k1_funct_1 @ sk_C @ X52))
% 1.93/2.10          | ~ (m1_subset_1 @ X52 @ (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('277', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | ~ (m1_subset_1 @ 
% 1.93/2.10             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10             (u1_struct_0 @ sk_A))
% 1.93/2.10        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.93/2.10            = (k1_funct_1 @ sk_C @ 
% 1.93/2.10               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.93/2.10      inference('sup-', [status(thm)], ['275', '276'])).
% 1.93/2.10  thf('278', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.93/2.10            = (k1_funct_1 @ sk_C @ 
% 1.93/2.10               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['274', '277'])).
% 1.93/2.10  thf('279', plain,
% 1.93/2.10      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.93/2.10          = (k1_funct_1 @ sk_C @ 
% 1.93/2.10             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['278'])).
% 1.93/2.10  thf('280', plain,
% 1.93/2.10      (((m1_subset_1 @ 
% 1.93/2.10         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10         (u1_struct_0 @ sk_A))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['273'])).
% 1.93/2.10  thf('281', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_hidden @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['242', '243'])).
% 1.93/2.10  thf(t95_tmap_1, axiom,
% 1.93/2.10    (![A:$i]:
% 1.93/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.10       ( ![B:$i]:
% 1.93/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.10           ( ![C:$i]:
% 1.93/2.10             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.10               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 1.93/2.10                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 1.93/2.10  thf('282', plain,
% 1.93/2.10      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X49)
% 1.93/2.10          | ~ (m1_pre_topc @ X49 @ X50)
% 1.93/2.10          | ~ (r2_hidden @ X51 @ (u1_struct_0 @ X49))
% 1.93/2.10          | ((k1_funct_1 @ (k4_tmap_1 @ X50 @ X49) @ X51) = (X51))
% 1.93/2.10          | ~ (m1_subset_1 @ X51 @ (u1_struct_0 @ X50))
% 1.93/2.10          | ~ (l1_pre_topc @ X50)
% 1.93/2.10          | ~ (v2_pre_topc @ X50)
% 1.93/2.10          | (v2_struct_0 @ X50))),
% 1.93/2.10      inference('cnf', [status(esa)], [t95_tmap_1])).
% 1.93/2.10  thf('283', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         ((v2_struct_0 @ sk_A)
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (v2_struct_0 @ X0)
% 1.93/2.10          | ~ (v2_pre_topc @ X0)
% 1.93/2.10          | ~ (l1_pre_topc @ X0)
% 1.93/2.10          | ~ (m1_subset_1 @ 
% 1.93/2.10               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10               (u1_struct_0 @ X0))
% 1.93/2.10          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 1.93/2.10              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.10          | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['281', '282'])).
% 1.93/2.10  thf('284', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.10          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 1.93/2.10              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10          | ~ (m1_subset_1 @ 
% 1.93/2.10               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10               (u1_struct_0 @ X0))
% 1.93/2.10          | ~ (l1_pre_topc @ X0)
% 1.93/2.10          | ~ (v2_pre_topc @ X0)
% 1.93/2.10          | (v2_struct_0 @ X0)
% 1.93/2.10          | (v2_struct_0 @ sk_B)
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10             (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10          | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['283'])).
% 1.93/2.10  thf('285', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.93/2.10      inference('sup-', [status(thm)], ['280', '284'])).
% 1.93/2.10  thf('286', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('287', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('288', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('289', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 1.93/2.10      inference('demod', [status(thm)], ['285', '286', '287', '288'])).
% 1.93/2.10  thf('290', plain,
% 1.93/2.10      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10          = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('simplify', [status(thm)], ['289'])).
% 1.93/2.10  thf('291', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_B)
% 1.93/2.10        | (m1_subset_1 @ 
% 1.93/2.10           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.93/2.10           (u1_struct_0 @ sk_B))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A))),
% 1.93/2.10      inference('demod', [status(thm)], ['265', '266'])).
% 1.93/2.10  thf('292', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf(redefinition_k3_funct_2, axiom,
% 1.93/2.10    (![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.10     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.93/2.10         ( v1_funct_2 @ C @ A @ B ) & 
% 1.93/2.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.93/2.10         ( m1_subset_1 @ D @ A ) ) =>
% 1.93/2.10       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.93/2.10  thf('293', plain,
% 1.93/2.10      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.93/2.10         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 1.93/2.10          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 1.93/2.10          | ~ (v1_funct_1 @ X3)
% 1.93/2.10          | (v1_xboole_0 @ X4)
% 1.93/2.10          | ~ (m1_subset_1 @ X6 @ X4)
% 1.93/2.10          | ((k3_funct_2 @ X4 @ X5 @ X3 @ X6) = (k1_funct_1 @ X3 @ X6)))),
% 1.93/2.10      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.93/2.10  thf('294', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10            X0) = (k1_funct_1 @ sk_C @ X0))
% 1.93/2.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.93/2.10          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.10          | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.93/2.10      inference('sup-', [status(thm)], ['292', '293'])).
% 1.93/2.10  thf('295', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('296', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('297', plain,
% 1.93/2.10      (![X0 : $i]:
% 1.93/2.10         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10            X0) = (k1_funct_1 @ sk_C @ X0))
% 1.93/2.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.93/2.10          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.93/2.10      inference('demod', [status(thm)], ['294', '295', '296'])).
% 1.93/2.10  thf('298', plain,
% 1.93/2.10      (((v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.10        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10            = (k1_funct_1 @ sk_C @ 
% 1.93/2.10               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.93/2.10      inference('sup-', [status(thm)], ['291', '297'])).
% 1.93/2.10  thf('299', plain,
% 1.93/2.10      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.93/2.10         ((v2_struct_0 @ X37)
% 1.93/2.10          | ~ (v2_pre_topc @ X37)
% 1.93/2.10          | ~ (l1_pre_topc @ X37)
% 1.93/2.10          | ~ (v1_funct_1 @ X38)
% 1.93/2.10          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 1.93/2.10          | ~ (m1_subset_1 @ X38 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 1.93/2.10          | ((k3_funct_2 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ X38 @ 
% 1.93/2.10              (sk_F @ X40 @ X38 @ X41 @ X37 @ X39))
% 1.93/2.10              != (k1_funct_1 @ X40 @ (sk_F @ X40 @ X38 @ X41 @ X37 @ X39)))
% 1.93/2.10          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39) @ 
% 1.93/2.10             (k2_tmap_1 @ X37 @ X39 @ X38 @ X41) @ X40)
% 1.93/2.10          | ~ (m1_subset_1 @ X40 @ 
% 1.93/2.10               (k1_zfmisc_1 @ 
% 1.93/2.10                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 1.93/2.10          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 1.93/2.10          | ~ (v1_funct_1 @ X40)
% 1.93/2.10          | ~ (m1_pre_topc @ X41 @ X37)
% 1.93/2.10          | (v2_struct_0 @ X41)
% 1.93/2.10          | ~ (l1_pre_topc @ X39)
% 1.93/2.10          | ~ (v2_pre_topc @ X39)
% 1.93/2.10          | (v2_struct_0 @ X39))),
% 1.93/2.10      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.93/2.10  thf('300', plain,
% 1.93/2.10      ((((k1_funct_1 @ sk_C @ 
% 1.93/2.10          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.93/2.10        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.10        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10             (u1_struct_0 @ sk_A))
% 1.93/2.10        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10             (k1_zfmisc_1 @ 
% 1.93/2.10              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.10           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | ~ (m1_subset_1 @ sk_C @ 
% 1.93/2.10             (k1_zfmisc_1 @ 
% 1.93/2.10              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.93/2.10        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.10        | ~ (v1_funct_1 @ sk_C)
% 1.93/2.10        | ~ (l1_pre_topc @ sk_B)
% 1.93/2.10        | ~ (v2_pre_topc @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['298', '299'])).
% 1.93/2.10  thf('301', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('302', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('303', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.93/2.10      inference('clc', [status(thm)], ['21', '22'])).
% 1.93/2.10  thf('304', plain,
% 1.93/2.10      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.93/2.10        (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('clc', [status(thm)], ['29', '30'])).
% 1.93/2.10  thf('305', plain,
% 1.93/2.10      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('clc', [status(thm)], ['6', '7'])).
% 1.93/2.10  thf('306', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 1.93/2.10      inference('clc', [status(thm)], ['235', '236'])).
% 1.93/2.10  thf('307', plain,
% 1.93/2.10      ((m1_subset_1 @ sk_C @ 
% 1.93/2.10        (k1_zfmisc_1 @ 
% 1.93/2.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('308', plain,
% 1.93/2.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('309', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.10  thf('310', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.10  thf('311', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.10      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.93/2.10  thf('312', plain,
% 1.93/2.10      ((((k1_funct_1 @ sk_C @ 
% 1.93/2.10          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.93/2.10        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B))),
% 1.93/2.10      inference('demod', [status(thm)],
% 1.93/2.10                ['300', '301', '302', '303', '304', '305', '306', '307', 
% 1.93/2.10                 '308', '309', '310', '311'])).
% 1.93/2.10  thf('313', plain,
% 1.93/2.10      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.10        | ((k1_funct_1 @ sk_C @ 
% 1.93/2.10            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10            != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.93/2.10                (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.93/2.10      inference('simplify', [status(thm)], ['312'])).
% 1.93/2.10  thf('314', plain,
% 1.93/2.10      ((((k1_funct_1 @ sk_C @ 
% 1.93/2.10          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 1.93/2.10      inference('sup-', [status(thm)], ['290', '313'])).
% 1.93/2.10  thf('315', plain,
% 1.93/2.10      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.10        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | ((k1_funct_1 @ sk_C @ 
% 1.93/2.10            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10            != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 1.93/2.10      inference('simplify', [status(thm)], ['314'])).
% 1.93/2.10  thf('316', plain,
% 1.93/2.10      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.93/2.10          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.10           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.10        | (v2_struct_0 @ sk_B)
% 1.93/2.10        | (v2_struct_0 @ sk_A)
% 1.93/2.10        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.11        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 1.93/2.11      inference('sup-', [status(thm)], ['279', '315'])).
% 1.93/2.11  thf('317', plain,
% 1.93/2.11      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 1.93/2.11        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ sk_A))),
% 1.93/2.11      inference('simplify', [status(thm)], ['316'])).
% 1.93/2.11  thf('318', plain,
% 1.93/2.11      ((~ (l1_pre_topc @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.93/2.11      inference('sup-', [status(thm)], ['245', '317'])).
% 1.93/2.11  thf('319', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.11      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.11  thf('320', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_A)
% 1.93/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.93/2.11      inference('demod', [status(thm)], ['318', '319'])).
% 1.93/2.11  thf('321', plain,
% 1.93/2.11      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.11        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11             (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.93/2.11      inference('demod', [status(thm)], ['15', '23', '31'])).
% 1.93/2.11  thf('322', plain,
% 1.93/2.11      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.93/2.11      inference('sup-', [status(thm)], ['320', '321'])).
% 1.93/2.11  thf('323', plain,
% 1.93/2.11      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.93/2.11          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('324', plain,
% 1.93/2.11      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11           sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.93/2.11      inference('sup-', [status(thm)], ['322', '323'])).
% 1.93/2.11  thf('325', plain,
% 1.93/2.11      ((m1_subset_1 @ sk_C @ 
% 1.93/2.11        (k1_zfmisc_1 @ 
% 1.93/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('326', plain,
% 1.93/2.11      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.93/2.11         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.93/2.11          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 1.93/2.11          | ~ (v1_funct_1 @ X7)
% 1.93/2.11          | ~ (v1_funct_1 @ X10)
% 1.93/2.11          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.93/2.11          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.93/2.11          | (r2_funct_2 @ X8 @ X9 @ X7 @ X10)
% 1.93/2.11          | ((X7) != (X10)))),
% 1.93/2.11      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.93/2.11  thf('327', plain,
% 1.93/2.11      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.93/2.11         ((r2_funct_2 @ X8 @ X9 @ X10 @ X10)
% 1.93/2.11          | ~ (v1_funct_1 @ X10)
% 1.93/2.11          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.93/2.11          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.93/2.11      inference('simplify', [status(thm)], ['326'])).
% 1.93/2.11  thf('328', plain,
% 1.93/2.11      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.93/2.11        | ~ (v1_funct_1 @ sk_C)
% 1.93/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11           sk_C))),
% 1.93/2.11      inference('sup-', [status(thm)], ['325', '327'])).
% 1.93/2.11  thf('329', plain,
% 1.93/2.11      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('330', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('331', plain,
% 1.93/2.11      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C)),
% 1.93/2.11      inference('demod', [status(thm)], ['328', '329', '330'])).
% 1.93/2.11  thf('332', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.93/2.11      inference('demod', [status(thm)], ['324', '331'])).
% 1.93/2.11  thf('333', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('334', plain,
% 1.93/2.11      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('clc', [status(thm)], ['332', '333'])).
% 1.93/2.11  thf('335', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('336', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.93/2.11      inference('clc', [status(thm)], ['334', '335'])).
% 1.93/2.11  thf('337', plain,
% 1.93/2.11      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.93/2.11      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.11  thf(t1_tsep_1, axiom,
% 1.93/2.11    (![A:$i]:
% 1.93/2.11     ( ( l1_pre_topc @ A ) =>
% 1.93/2.11       ( ![B:$i]:
% 1.93/2.11         ( ( m1_pre_topc @ B @ A ) =>
% 1.93/2.11           ( m1_subset_1 @
% 1.93/2.11             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.93/2.11  thf('338', plain,
% 1.93/2.11      (![X34 : $i, X35 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ X34 @ X35)
% 1.93/2.11          | (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 1.93/2.11             (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.93/2.11          | ~ (l1_pre_topc @ X35))),
% 1.93/2.11      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.93/2.11  thf('339', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         (~ (l1_pre_topc @ X0)
% 1.93/2.11          | ~ (l1_pre_topc @ X0)
% 1.93/2.11          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.93/2.11             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.93/2.11      inference('sup-', [status(thm)], ['337', '338'])).
% 1.93/2.11  thf('340', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.93/2.11           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.93/2.11          | ~ (l1_pre_topc @ X0))),
% 1.93/2.11      inference('simplify', [status(thm)], ['339'])).
% 1.93/2.11  thf(t5_subset, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i]:
% 1.93/2.11     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.93/2.11          ( v1_xboole_0 @ C ) ) ))).
% 1.93/2.11  thf('341', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.11         (~ (r2_hidden @ X0 @ X1)
% 1.93/2.11          | ~ (v1_xboole_0 @ X2)
% 1.93/2.11          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 1.93/2.11      inference('cnf', [status(esa)], [t5_subset])).
% 1.93/2.11  thf('342', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]:
% 1.93/2.11         (~ (l1_pre_topc @ X0)
% 1.93/2.11          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.93/2.11          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 1.93/2.11      inference('sup-', [status(thm)], ['340', '341'])).
% 1.93/2.11  thf('343', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)) | ~ (l1_pre_topc @ sk_B))),
% 1.93/2.11      inference('sup-', [status(thm)], ['336', '342'])).
% 1.93/2.11  thf('344', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.11      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.11  thf('345', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B))),
% 1.93/2.11      inference('demod', [status(thm)], ['343', '344'])).
% 1.93/2.11  thf('346', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_A)
% 1.93/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11           (k4_tmap_1 @ sk_A @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('sup-', [status(thm)], ['244', '345'])).
% 1.93/2.11  thf('347', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('348', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_B)
% 1.93/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11           (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.93/2.11      inference('clc', [status(thm)], ['346', '347'])).
% 1.93/2.11  thf('349', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('350', plain,
% 1.93/2.11      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.93/2.11        (k4_tmap_1 @ sk_A @ sk_B))),
% 1.93/2.11      inference('clc', [status(thm)], ['348', '349'])).
% 1.93/2.11  thf('351', plain, (((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))),
% 1.93/2.11      inference('demod', [status(thm)], ['32', '350'])).
% 1.93/2.11  thf('352', plain,
% 1.93/2.11      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C)),
% 1.93/2.11      inference('demod', [status(thm)], ['328', '329', '330'])).
% 1.93/2.11  thf('353', plain, ($false),
% 1.93/2.11      inference('demod', [status(thm)], ['0', '351', '352'])).
% 1.93/2.11  
% 1.93/2.11  % SZS output end Refutation
% 1.93/2.11  
% 1.93/2.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
