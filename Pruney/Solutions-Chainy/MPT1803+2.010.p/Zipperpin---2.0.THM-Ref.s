%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IiHToYuYzX

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:00 EST 2020

% Result     : Theorem 3.81s
% Output     : Refutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  232 (1649 expanded)
%              Number of leaves         :   47 ( 495 expanded)
%              Depth                    :   25
%              Number of atoms          : 2347 (29908 expanded)
%              Number of equality atoms :   41 ( 212 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t119_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tmap_1 @ B @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( r1_tmap_1 @ B @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t119_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_pre_topc @ X45 @ X46 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X36 @ X35 ) )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k8_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( C
                        = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( X21
       != ( k8_tmap_1 @ X20 @ X19 ) )
      | ( X22
       != ( u1_struct_0 @ X19 ) )
      | ( X21
        = ( k6_tmap_1 @ X20 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( v1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X20 @ X19 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k8_tmap_1 @ X20 @ X19 )
        = ( k6_tmap_1 @ X20 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_pre_topc @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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

thf('23',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('24',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('32',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('40',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','29','37','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','50'])).

thf(d12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) )
             => ( ( C
                  = ( k9_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( X25
       != ( k9_tmap_1 @ X24 @ X23 ) )
      | ( X26
       != ( u1_struct_0 @ X23 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X23 ) ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X24 @ X26 ) ) @ X25 @ ( k7_tmap_1 @ X24 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X23 ) ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('53',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X24 @ X23 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X23 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X24 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X23 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X23 ) ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X24 @ ( u1_struct_0 @ X23 ) ) ) @ ( k9_tmap_1 @ X24 @ X23 ) @ ( k7_tmap_1 @ X24 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k9_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X33 @ X34 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','50'])).

thf('64',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','50'])).

thf('67',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('68',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','50'])).

thf('69',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('70',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','50'])).

thf('71',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X33 @ X34 ) @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('73',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','50'])).

thf('80',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('83',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','64','65','66','67','68','69','70','80','88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

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

thf('95',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( X13 = X17 )
      | ~ ( r1_funct_2 @ X14 @ X15 @ X18 @ X16 @ X13 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('98',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('103',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('110',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('111',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('119',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X30 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('120',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('122',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','50'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['100','108','117','127'])).

thf('129',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t110_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( ( u1_struct_0 @ C )
                  = B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf('132',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( u1_struct_0 @ X39 )
       != X37 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ( r1_tmap_1 @ X39 @ ( k6_tmap_1 @ X38 @ X37 ) @ ( k2_tmap_1 @ X38 @ ( k6_tmap_1 @ X38 @ X37 ) @ ( k7_tmap_1 @ X38 @ X37 ) @ X39 ) @ X40 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t110_tmap_1])).

thf('133',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ( r1_tmap_1 @ X39 @ ( k6_tmap_1 @ X38 @ ( u1_struct_0 @ X39 ) ) @ ( k2_tmap_1 @ X38 @ ( k6_tmap_1 @ X38 @ ( u1_struct_0 @ X39 ) ) @ ( k7_tmap_1 @ X38 @ ( u1_struct_0 @ X39 ) ) @ X39 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_tmap_1 @ sk_B_1 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','133'])).

thf('135',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('136',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('137',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['130','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['129','145'])).

thf('147',plain,(
    ~ ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','148'])).

thf('150',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','149'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('151',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('154',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ( r1_tsep_1 @ X28 @ X27 )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_tsep_1 @ X0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','155'])).

thf('157',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('158',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('159',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['159','160'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('162',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('163',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( r1_tsep_1 @ X0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['156','163'])).

thf('165',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf('168',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( m1_pre_topc @ X41 @ X42 )
      | ~ ( r1_tsep_1 @ X41 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X43 ) )
      | ( r1_tmap_1 @ X43 @ ( k8_tmap_1 @ X42 @ X41 ) @ ( k2_tmap_1 @ X42 @ ( k8_tmap_1 @ X42 @ X41 ) @ ( k9_tmap_1 @ X42 @ X41 ) @ X43 ) @ X44 )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t118_tmap_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ X0 @ X1 ) @ ( k2_tmap_1 @ X0 @ ( k8_tmap_1 @ X0 @ X1 ) @ ( k9_tmap_1 @ X0 @ X1 ) @ sk_B_1 ) @ sk_C_1 )
      | ~ ( r1_tsep_1 @ X1 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B_1 )
      | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ X0 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ X0 ) @ ( k9_tmap_1 @ sk_A @ X0 ) @ sk_B_1 ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','169'])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_B_1 )
      | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ X0 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ X0 ) @ ( k9_tmap_1 @ sk_A @ X0 ) @ sk_B_1 ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C_1 )
    | ~ ( r1_tsep_1 @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['165','173'])).

thf('175',plain,
    ( ~ ( r1_tsep_1 @ sk_B_1 @ sk_B_1 )
    | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['164','175'])).

thf('177',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['161','162'])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,(
    $false ),
    inference(demod,[status(thm)],['0','182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IiHToYuYzX
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.81/4.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.81/4.03  % Solved by: fo/fo7.sh
% 3.81/4.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.81/4.03  % done 1824 iterations in 3.571s
% 3.81/4.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.81/4.03  % SZS output start Refutation
% 3.81/4.03  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 3.81/4.03  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 3.81/4.03  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 3.81/4.03  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 3.81/4.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.81/4.03  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.81/4.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.81/4.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.81/4.03  thf(sk_B_type, type, sk_B: $i > $i).
% 3.81/4.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.81/4.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.81/4.03  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 3.81/4.03  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 3.81/4.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.81/4.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.81/4.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.81/4.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.81/4.03  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 3.81/4.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.81/4.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.81/4.03  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.81/4.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.81/4.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.81/4.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.81/4.03  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 3.81/4.03  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 3.81/4.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.81/4.03  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 3.81/4.03  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 3.81/4.03  thf(sk_A_type, type, sk_A: $i).
% 3.81/4.03  thf(t119_tmap_1, conjecture,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.81/4.03       ( ![B:$i]:
% 3.81/4.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.81/4.03           ( ![C:$i]:
% 3.81/4.03             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 3.81/4.03               ( r1_tmap_1 @
% 3.81/4.03                 B @ ( k8_tmap_1 @ A @ B ) @ 
% 3.81/4.03                 ( k2_tmap_1 @
% 3.81/4.03                   A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 3.81/4.03                 C ) ) ) ) ) ))).
% 3.81/4.03  thf(zf_stmt_0, negated_conjecture,
% 3.81/4.03    (~( ![A:$i]:
% 3.81/4.03        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.81/4.03            ( l1_pre_topc @ A ) ) =>
% 3.81/4.03          ( ![B:$i]:
% 3.81/4.03            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.81/4.03              ( ![C:$i]:
% 3.81/4.03                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 3.81/4.03                  ( r1_tmap_1 @
% 3.81/4.03                    B @ ( k8_tmap_1 @ A @ B ) @ 
% 3.81/4.03                    ( k2_tmap_1 @
% 3.81/4.03                      A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 3.81/4.03                    C ) ) ) ) ) ) )),
% 3.81/4.03    inference('cnf.neg', [status(esa)], [t119_tmap_1])).
% 3.81/4.03  thf('0', plain, (~ (v2_struct_0 @ sk_B_1)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf(d1_xboole_0, axiom,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.81/4.03  thf('1', plain,
% 3.81/4.03      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.81/4.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.81/4.03  thf('2', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf(t1_tsep_1, axiom,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( l1_pre_topc @ A ) =>
% 3.81/4.03       ( ![B:$i]:
% 3.81/4.03         ( ( m1_pre_topc @ B @ A ) =>
% 3.81/4.03           ( m1_subset_1 @
% 3.81/4.03             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.81/4.03  thf('3', plain,
% 3.81/4.03      (![X45 : $i, X46 : $i]:
% 3.81/4.03         (~ (m1_pre_topc @ X45 @ X46)
% 3.81/4.03          | (m1_subset_1 @ (u1_struct_0 @ X45) @ 
% 3.81/4.03             (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 3.81/4.03          | ~ (l1_pre_topc @ X46))),
% 3.81/4.03      inference('cnf', [status(esa)], [t1_tsep_1])).
% 3.81/4.03  thf('4', plain,
% 3.81/4.03      ((~ (l1_pre_topc @ sk_A)
% 3.81/4.03        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.81/4.03      inference('sup-', [status(thm)], ['2', '3'])).
% 3.81/4.03  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('6', plain,
% 3.81/4.03      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('demod', [status(thm)], ['4', '5'])).
% 3.81/4.03  thf(t5_subset, axiom,
% 3.81/4.03    (![A:$i,B:$i,C:$i]:
% 3.81/4.03     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.81/4.03          ( v1_xboole_0 @ C ) ) ))).
% 3.81/4.03  thf('7', plain,
% 3.81/4.03      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.81/4.03         (~ (r2_hidden @ X7 @ X8)
% 3.81/4.03          | ~ (v1_xboole_0 @ X9)
% 3.81/4.03          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 3.81/4.03      inference('cnf', [status(esa)], [t5_subset])).
% 3.81/4.03  thf('8', plain,
% 3.81/4.03      (![X0 : $i]:
% 3.81/4.03         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.81/4.03          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 3.81/4.03      inference('sup-', [status(thm)], ['6', '7'])).
% 3.81/4.03  thf('9', plain,
% 3.81/4.03      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('demod', [status(thm)], ['4', '5'])).
% 3.81/4.03  thf(t104_tmap_1, axiom,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.81/4.03       ( ![B:$i]:
% 3.81/4.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.81/4.03           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 3.81/4.03             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 3.81/4.03  thf('10', plain,
% 3.81/4.03      (![X35 : $i, X36 : $i]:
% 3.81/4.03         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 3.81/4.03          | ((u1_struct_0 @ (k6_tmap_1 @ X36 @ X35)) = (u1_struct_0 @ X36))
% 3.81/4.03          | ~ (l1_pre_topc @ X36)
% 3.81/4.03          | ~ (v2_pre_topc @ X36)
% 3.81/4.03          | (v2_struct_0 @ X36))),
% 3.81/4.03      inference('cnf', [status(esa)], [t104_tmap_1])).
% 3.81/4.03  thf('11', plain,
% 3.81/4.03      (((v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A)
% 3.81/4.03        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03            = (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('sup-', [status(thm)], ['9', '10'])).
% 3.81/4.03  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('14', plain,
% 3.81/4.03      (((v2_struct_0 @ sk_A)
% 3.81/4.03        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03            = (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('demod', [status(thm)], ['11', '12', '13'])).
% 3.81/4.03  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('16', plain,
% 3.81/4.03      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03         = (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('clc', [status(thm)], ['14', '15'])).
% 3.81/4.03  thf('17', plain,
% 3.81/4.03      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('demod', [status(thm)], ['4', '5'])).
% 3.81/4.03  thf(d11_tmap_1, axiom,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.81/4.03       ( ![B:$i]:
% 3.81/4.03         ( ( m1_pre_topc @ B @ A ) =>
% 3.81/4.03           ( ![C:$i]:
% 3.81/4.03             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 3.81/4.03                 ( l1_pre_topc @ C ) ) =>
% 3.81/4.03               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 3.81/4.03                 ( ![D:$i]:
% 3.81/4.03                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.81/4.03                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 3.81/4.03                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.81/4.03  thf('18', plain,
% 3.81/4.03      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.81/4.03         (~ (m1_pre_topc @ X19 @ X20)
% 3.81/4.03          | ((X21) != (k8_tmap_1 @ X20 @ X19))
% 3.81/4.03          | ((X22) != (u1_struct_0 @ X19))
% 3.81/4.03          | ((X21) = (k6_tmap_1 @ X20 @ X22))
% 3.81/4.03          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.81/4.03          | ~ (l1_pre_topc @ X21)
% 3.81/4.03          | ~ (v2_pre_topc @ X21)
% 3.81/4.03          | ~ (v1_pre_topc @ X21)
% 3.81/4.03          | ~ (l1_pre_topc @ X20)
% 3.81/4.03          | ~ (v2_pre_topc @ X20)
% 3.81/4.03          | (v2_struct_0 @ X20))),
% 3.81/4.03      inference('cnf', [status(esa)], [d11_tmap_1])).
% 3.81/4.03  thf('19', plain,
% 3.81/4.03      (![X19 : $i, X20 : $i]:
% 3.81/4.03         ((v2_struct_0 @ X20)
% 3.81/4.03          | ~ (v2_pre_topc @ X20)
% 3.81/4.03          | ~ (l1_pre_topc @ X20)
% 3.81/4.03          | ~ (v1_pre_topc @ (k8_tmap_1 @ X20 @ X19))
% 3.81/4.03          | ~ (v2_pre_topc @ (k8_tmap_1 @ X20 @ X19))
% 3.81/4.03          | ~ (l1_pre_topc @ (k8_tmap_1 @ X20 @ X19))
% 3.81/4.03          | ~ (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 3.81/4.03               (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.81/4.03          | ((k8_tmap_1 @ X20 @ X19) = (k6_tmap_1 @ X20 @ (u1_struct_0 @ X19)))
% 3.81/4.03          | ~ (m1_pre_topc @ X19 @ X20))),
% 3.81/4.03      inference('simplify', [status(thm)], ['18'])).
% 3.81/4.03  thf('20', plain,
% 3.81/4.03      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 3.81/4.03        | ((k8_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 3.81/4.03        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 3.81/4.03        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['17', '19'])).
% 3.81/4.03  thf('21', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('22', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf(dt_k8_tmap_1, axiom,
% 3.81/4.03    (![A:$i,B:$i]:
% 3.81/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.81/4.03         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.81/4.03       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 3.81/4.03         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 3.81/4.03         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 3.81/4.03  thf('23', plain,
% 3.81/4.03      (![X31 : $i, X32 : $i]:
% 3.81/4.03         (~ (l1_pre_topc @ X31)
% 3.81/4.03          | ~ (v2_pre_topc @ X31)
% 3.81/4.03          | (v2_struct_0 @ X31)
% 3.81/4.03          | ~ (m1_pre_topc @ X32 @ X31)
% 3.81/4.03          | (l1_pre_topc @ (k8_tmap_1 @ X31 @ X32)))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 3.81/4.03  thf('24', plain,
% 3.81/4.03      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['22', '23'])).
% 3.81/4.03  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('27', plain,
% 3.81/4.03      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['24', '25', '26'])).
% 3.81/4.03  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('29', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 3.81/4.03      inference('clc', [status(thm)], ['27', '28'])).
% 3.81/4.03  thf('30', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('31', plain,
% 3.81/4.03      (![X31 : $i, X32 : $i]:
% 3.81/4.03         (~ (l1_pre_topc @ X31)
% 3.81/4.03          | ~ (v2_pre_topc @ X31)
% 3.81/4.03          | (v2_struct_0 @ X31)
% 3.81/4.03          | ~ (m1_pre_topc @ X32 @ X31)
% 3.81/4.03          | (v2_pre_topc @ (k8_tmap_1 @ X31 @ X32)))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 3.81/4.03  thf('32', plain,
% 3.81/4.03      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['30', '31'])).
% 3.81/4.03  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('35', plain,
% 3.81/4.03      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['32', '33', '34'])).
% 3.81/4.03  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('37', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 3.81/4.03      inference('clc', [status(thm)], ['35', '36'])).
% 3.81/4.03  thf('38', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('39', plain,
% 3.81/4.03      (![X31 : $i, X32 : $i]:
% 3.81/4.03         (~ (l1_pre_topc @ X31)
% 3.81/4.03          | ~ (v2_pre_topc @ X31)
% 3.81/4.03          | (v2_struct_0 @ X31)
% 3.81/4.03          | ~ (m1_pre_topc @ X32 @ X31)
% 3.81/4.03          | (v1_pre_topc @ (k8_tmap_1 @ X31 @ X32)))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 3.81/4.03  thf('40', plain,
% 3.81/4.03      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['38', '39'])).
% 3.81/4.03  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('43', plain,
% 3.81/4.03      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['40', '41', '42'])).
% 3.81/4.03  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('45', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 3.81/4.03      inference('clc', [status(thm)], ['43', '44'])).
% 3.81/4.03  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('48', plain,
% 3.81/4.03      ((((k8_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)],
% 3.81/4.03                ['20', '21', '29', '37', '45', '46', '47'])).
% 3.81/4.03  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('50', plain,
% 3.81/4.03      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 3.81/4.03      inference('clc', [status(thm)], ['48', '49'])).
% 3.81/4.03  thf('51', plain,
% 3.81/4.03      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['16', '50'])).
% 3.81/4.03  thf(d12_tmap_1, axiom,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.81/4.03       ( ![B:$i]:
% 3.81/4.03         ( ( m1_pre_topc @ B @ A ) =>
% 3.81/4.03           ( ![C:$i]:
% 3.81/4.03             ( ( ( v1_funct_1 @ C ) & 
% 3.81/4.03                 ( v1_funct_2 @
% 3.81/4.03                   C @ ( u1_struct_0 @ A ) @ 
% 3.81/4.03                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 3.81/4.03                 ( m1_subset_1 @
% 3.81/4.03                   C @ 
% 3.81/4.03                   ( k1_zfmisc_1 @
% 3.81/4.03                     ( k2_zfmisc_1 @
% 3.81/4.03                       ( u1_struct_0 @ A ) @ 
% 3.81/4.03                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 3.81/4.03               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 3.81/4.03                 ( ![D:$i]:
% 3.81/4.03                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.81/4.03                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 3.81/4.03                       ( r1_funct_2 @
% 3.81/4.03                         ( u1_struct_0 @ A ) @ 
% 3.81/4.03                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 3.81/4.03                         ( u1_struct_0 @ A ) @ 
% 3.81/4.03                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 3.81/4.03                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.81/4.03  thf('52', plain,
% 3.81/4.03      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.81/4.03         (~ (m1_pre_topc @ X23 @ X24)
% 3.81/4.03          | ((X25) != (k9_tmap_1 @ X24 @ X23))
% 3.81/4.03          | ((X26) != (u1_struct_0 @ X23))
% 3.81/4.03          | (r1_funct_2 @ (u1_struct_0 @ X24) @ 
% 3.81/4.03             (u1_struct_0 @ (k8_tmap_1 @ X24 @ X23)) @ (u1_struct_0 @ X24) @ 
% 3.81/4.03             (u1_struct_0 @ (k6_tmap_1 @ X24 @ X26)) @ X25 @ 
% 3.81/4.03             (k7_tmap_1 @ X24 @ X26))
% 3.81/4.03          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 3.81/4.03          | ~ (m1_subset_1 @ X25 @ 
% 3.81/4.03               (k1_zfmisc_1 @ 
% 3.81/4.03                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ 
% 3.81/4.03                 (u1_struct_0 @ (k8_tmap_1 @ X24 @ X23)))))
% 3.81/4.03          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ 
% 3.81/4.03               (u1_struct_0 @ (k8_tmap_1 @ X24 @ X23)))
% 3.81/4.03          | ~ (v1_funct_1 @ X25)
% 3.81/4.03          | ~ (l1_pre_topc @ X24)
% 3.81/4.03          | ~ (v2_pre_topc @ X24)
% 3.81/4.03          | (v2_struct_0 @ X24))),
% 3.81/4.03      inference('cnf', [status(esa)], [d12_tmap_1])).
% 3.81/4.03  thf('53', plain,
% 3.81/4.03      (![X23 : $i, X24 : $i]:
% 3.81/4.03         ((v2_struct_0 @ X24)
% 3.81/4.03          | ~ (v2_pre_topc @ X24)
% 3.81/4.03          | ~ (l1_pre_topc @ X24)
% 3.81/4.03          | ~ (v1_funct_1 @ (k9_tmap_1 @ X24 @ X23))
% 3.81/4.03          | ~ (v1_funct_2 @ (k9_tmap_1 @ X24 @ X23) @ (u1_struct_0 @ X24) @ 
% 3.81/4.03               (u1_struct_0 @ (k8_tmap_1 @ X24 @ X23)))
% 3.81/4.03          | ~ (m1_subset_1 @ (k9_tmap_1 @ X24 @ X23) @ 
% 3.81/4.03               (k1_zfmisc_1 @ 
% 3.81/4.03                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ 
% 3.81/4.03                 (u1_struct_0 @ (k8_tmap_1 @ X24 @ X23)))))
% 3.81/4.03          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 3.81/4.03               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 3.81/4.03          | (r1_funct_2 @ (u1_struct_0 @ X24) @ 
% 3.81/4.03             (u1_struct_0 @ (k8_tmap_1 @ X24 @ X23)) @ (u1_struct_0 @ X24) @ 
% 3.81/4.03             (u1_struct_0 @ (k6_tmap_1 @ X24 @ (u1_struct_0 @ X23))) @ 
% 3.81/4.03             (k9_tmap_1 @ X24 @ X23) @ (k7_tmap_1 @ X24 @ (u1_struct_0 @ X23)))
% 3.81/4.03          | ~ (m1_pre_topc @ X23 @ X24))),
% 3.81/4.03      inference('simplify', [status(thm)], ['52'])).
% 3.81/4.03  thf('54', plain,
% 3.81/4.03      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03           (k1_zfmisc_1 @ 
% 3.81/4.03            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.81/4.03        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 3.81/4.03        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ 
% 3.81/4.03           (u1_struct_0 @ sk_A) @ 
% 3.81/4.03           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))) @ 
% 3.81/4.03           (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.81/4.03        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 3.81/4.03        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['51', '53'])).
% 3.81/4.03  thf('55', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf(dt_k9_tmap_1, axiom,
% 3.81/4.03    (![A:$i,B:$i]:
% 3.81/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.81/4.03         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.81/4.03       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 3.81/4.03         ( v1_funct_2 @
% 3.81/4.03           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.81/4.03           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 3.81/4.03         ( m1_subset_1 @
% 3.81/4.03           ( k9_tmap_1 @ A @ B ) @ 
% 3.81/4.03           ( k1_zfmisc_1 @
% 3.81/4.03             ( k2_zfmisc_1 @
% 3.81/4.03               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 3.81/4.03  thf('56', plain,
% 3.81/4.03      (![X33 : $i, X34 : $i]:
% 3.81/4.03         (~ (l1_pre_topc @ X33)
% 3.81/4.03          | ~ (v2_pre_topc @ X33)
% 3.81/4.03          | (v2_struct_0 @ X33)
% 3.81/4.03          | ~ (m1_pre_topc @ X34 @ X33)
% 3.81/4.03          | (m1_subset_1 @ (k9_tmap_1 @ X33 @ X34) @ 
% 3.81/4.03             (k1_zfmisc_1 @ 
% 3.81/4.03              (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ 
% 3.81/4.03               (u1_struct_0 @ (k8_tmap_1 @ X33 @ X34))))))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 3.81/4.03  thf('57', plain,
% 3.81/4.03      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03         (k1_zfmisc_1 @ 
% 3.81/4.03          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['55', '56'])).
% 3.81/4.03  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('60', plain,
% 3.81/4.03      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03         (k1_zfmisc_1 @ 
% 3.81/4.03          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['57', '58', '59'])).
% 3.81/4.03  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('62', plain,
% 3.81/4.03      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ 
% 3.81/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 3.81/4.03      inference('clc', [status(thm)], ['60', '61'])).
% 3.81/4.03  thf('63', plain,
% 3.81/4.03      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['16', '50'])).
% 3.81/4.03  thf('64', plain,
% 3.81/4.03      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ 
% 3.81/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.81/4.03      inference('demod', [status(thm)], ['62', '63'])).
% 3.81/4.03  thf('65', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('66', plain,
% 3.81/4.03      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['16', '50'])).
% 3.81/4.03  thf('67', plain,
% 3.81/4.03      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 3.81/4.03      inference('clc', [status(thm)], ['48', '49'])).
% 3.81/4.03  thf('68', plain,
% 3.81/4.03      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['16', '50'])).
% 3.81/4.03  thf('69', plain,
% 3.81/4.03      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('demod', [status(thm)], ['4', '5'])).
% 3.81/4.03  thf('70', plain,
% 3.81/4.03      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['16', '50'])).
% 3.81/4.03  thf('71', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('72', plain,
% 3.81/4.03      (![X33 : $i, X34 : $i]:
% 3.81/4.03         (~ (l1_pre_topc @ X33)
% 3.81/4.03          | ~ (v2_pre_topc @ X33)
% 3.81/4.03          | (v2_struct_0 @ X33)
% 3.81/4.03          | ~ (m1_pre_topc @ X34 @ X33)
% 3.81/4.03          | (v1_funct_2 @ (k9_tmap_1 @ X33 @ X34) @ (u1_struct_0 @ X33) @ 
% 3.81/4.03             (u1_struct_0 @ (k8_tmap_1 @ X33 @ X34))))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 3.81/4.03  thf('73', plain,
% 3.81/4.03      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['71', '72'])).
% 3.81/4.03  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('76', plain,
% 3.81/4.03      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['73', '74', '75'])).
% 3.81/4.03  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('78', plain,
% 3.81/4.03      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 3.81/4.03      inference('clc', [status(thm)], ['76', '77'])).
% 3.81/4.03  thf('79', plain,
% 3.81/4.03      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['16', '50'])).
% 3.81/4.03  thf('80', plain,
% 3.81/4.03      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03        (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['78', '79'])).
% 3.81/4.03  thf('81', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('82', plain,
% 3.81/4.03      (![X33 : $i, X34 : $i]:
% 3.81/4.03         (~ (l1_pre_topc @ X33)
% 3.81/4.03          | ~ (v2_pre_topc @ X33)
% 3.81/4.03          | (v2_struct_0 @ X33)
% 3.81/4.03          | ~ (m1_pre_topc @ X34 @ X33)
% 3.81/4.03          | (v1_funct_1 @ (k9_tmap_1 @ X33 @ X34)))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 3.81/4.03  thf('83', plain,
% 3.81/4.03      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['81', '82'])).
% 3.81/4.03  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('86', plain,
% 3.81/4.03      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['83', '84', '85'])).
% 3.81/4.03  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('88', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 3.81/4.03      inference('clc', [status(thm)], ['86', '87'])).
% 3.81/4.03  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('91', plain,
% 3.81/4.03      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03         (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)],
% 3.81/4.03                ['54', '64', '65', '66', '67', '68', '69', '70', '80', '88', 
% 3.81/4.03                 '89', '90'])).
% 3.81/4.03  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('93', plain,
% 3.81/4.03      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03        (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03        (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 3.81/4.03      inference('clc', [status(thm)], ['91', '92'])).
% 3.81/4.03  thf('94', plain,
% 3.81/4.03      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ 
% 3.81/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.81/4.03      inference('demod', [status(thm)], ['62', '63'])).
% 3.81/4.03  thf(redefinition_r1_funct_2, axiom,
% 3.81/4.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.81/4.03     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 3.81/4.03         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 3.81/4.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.81/4.03         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 3.81/4.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.81/4.03       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 3.81/4.03  thf('95', plain,
% 3.81/4.03      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.81/4.03         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 3.81/4.03          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 3.81/4.03          | ~ (v1_funct_1 @ X13)
% 3.81/4.03          | (v1_xboole_0 @ X16)
% 3.81/4.03          | (v1_xboole_0 @ X15)
% 3.81/4.03          | ~ (v1_funct_1 @ X17)
% 3.81/4.03          | ~ (v1_funct_2 @ X17 @ X18 @ X16)
% 3.81/4.03          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 3.81/4.03          | ((X13) = (X17))
% 3.81/4.03          | ~ (r1_funct_2 @ X14 @ X15 @ X18 @ X16 @ X13 @ X17))),
% 3.81/4.03      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 3.81/4.03  thf('96', plain,
% 3.81/4.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.81/4.03         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 3.81/4.03             X1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 3.81/4.03          | ((k9_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 3.81/4.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.81/4.03          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 3.81/4.03          | ~ (v1_funct_1 @ X0)
% 3.81/4.03          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.81/4.03          | (v1_xboole_0 @ X1)
% 3.81/4.03          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 3.81/4.03          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('sup-', [status(thm)], ['94', '95'])).
% 3.81/4.03  thf('97', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 3.81/4.03      inference('clc', [status(thm)], ['86', '87'])).
% 3.81/4.03  thf('98', plain,
% 3.81/4.03      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03        (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['78', '79'])).
% 3.81/4.03  thf('99', plain,
% 3.81/4.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.81/4.03         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 3.81/4.03             X1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 3.81/4.03          | ((k9_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 3.81/4.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.81/4.03          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 3.81/4.03          | ~ (v1_funct_1 @ X0)
% 3.81/4.03          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.81/4.03          | (v1_xboole_0 @ X1))),
% 3.81/4.03      inference('demod', [status(thm)], ['96', '97', '98'])).
% 3.81/4.03  thf('100', plain,
% 3.81/4.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.81/4.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.81/4.03        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.81/4.03        | ~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03             (k1_zfmisc_1 @ 
% 3.81/4.03              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.81/4.03        | ((k9_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 3.81/4.03      inference('sup-', [status(thm)], ['93', '99'])).
% 3.81/4.03  thf('101', plain,
% 3.81/4.03      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('demod', [status(thm)], ['4', '5'])).
% 3.81/4.03  thf(dt_k7_tmap_1, axiom,
% 3.81/4.03    (![A:$i,B:$i]:
% 3.81/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.81/4.03         ( l1_pre_topc @ A ) & 
% 3.81/4.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.81/4.03       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 3.81/4.03         ( v1_funct_2 @
% 3.81/4.03           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.81/4.03           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 3.81/4.03         ( m1_subset_1 @
% 3.81/4.03           ( k7_tmap_1 @ A @ B ) @ 
% 3.81/4.03           ( k1_zfmisc_1 @
% 3.81/4.03             ( k2_zfmisc_1 @
% 3.81/4.03               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 3.81/4.03  thf('102', plain,
% 3.81/4.03      (![X29 : $i, X30 : $i]:
% 3.81/4.03         (~ (l1_pre_topc @ X29)
% 3.81/4.03          | ~ (v2_pre_topc @ X29)
% 3.81/4.03          | (v2_struct_0 @ X29)
% 3.81/4.03          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.81/4.03          | (v1_funct_1 @ (k7_tmap_1 @ X29 @ X30)))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.81/4.03  thf('103', plain,
% 3.81/4.03      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['101', '102'])).
% 3.81/4.03  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('106', plain,
% 3.81/4.03      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['103', '104', '105'])).
% 3.81/4.03  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('108', plain,
% 3.81/4.03      ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 3.81/4.03      inference('clc', [status(thm)], ['106', '107'])).
% 3.81/4.03  thf('109', plain,
% 3.81/4.03      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('demod', [status(thm)], ['4', '5'])).
% 3.81/4.03  thf('110', plain,
% 3.81/4.03      (![X29 : $i, X30 : $i]:
% 3.81/4.03         (~ (l1_pre_topc @ X29)
% 3.81/4.03          | ~ (v2_pre_topc @ X29)
% 3.81/4.03          | (v2_struct_0 @ X29)
% 3.81/4.03          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.81/4.03          | (v1_funct_2 @ (k7_tmap_1 @ X29 @ X30) @ (u1_struct_0 @ X29) @ 
% 3.81/4.03             (u1_struct_0 @ (k6_tmap_1 @ X29 @ X30))))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.81/4.03  thf('111', plain,
% 3.81/4.03      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03         (u1_struct_0 @ sk_A) @ 
% 3.81/4.03         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['109', '110'])).
% 3.81/4.03  thf('112', plain,
% 3.81/4.03      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03         = (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('clc', [status(thm)], ['14', '15'])).
% 3.81/4.03  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('115', plain,
% 3.81/4.03      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 3.81/4.03  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('117', plain,
% 3.81/4.03      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('clc', [status(thm)], ['115', '116'])).
% 3.81/4.03  thf('118', plain,
% 3.81/4.03      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('demod', [status(thm)], ['4', '5'])).
% 3.81/4.03  thf('119', plain,
% 3.81/4.03      (![X29 : $i, X30 : $i]:
% 3.81/4.03         (~ (l1_pre_topc @ X29)
% 3.81/4.03          | ~ (v2_pre_topc @ X29)
% 3.81/4.03          | (v2_struct_0 @ X29)
% 3.81/4.03          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.81/4.03          | (m1_subset_1 @ (k7_tmap_1 @ X29 @ X30) @ 
% 3.81/4.03             (k1_zfmisc_1 @ 
% 3.81/4.03              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ 
% 3.81/4.03               (u1_struct_0 @ (k6_tmap_1 @ X29 @ X30))))))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.81/4.03  thf('120', plain,
% 3.81/4.03      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03         (k1_zfmisc_1 @ 
% 3.81/4.03          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.81/4.03           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))))
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['118', '119'])).
% 3.81/4.03  thf('121', plain,
% 3.81/4.03      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 3.81/4.03      inference('clc', [status(thm)], ['48', '49'])).
% 3.81/4.03  thf('122', plain,
% 3.81/4.03      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['16', '50'])).
% 3.81/4.03  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('125', plain,
% 3.81/4.03      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03         (k1_zfmisc_1 @ 
% 3.81/4.03          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 3.81/4.03  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('127', plain,
% 3.81/4.03      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03        (k1_zfmisc_1 @ 
% 3.81/4.03         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.81/4.03      inference('clc', [status(thm)], ['125', '126'])).
% 3.81/4.03  thf('128', plain,
% 3.81/4.03      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.81/4.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.81/4.03        | ((k9_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 3.81/4.03      inference('demod', [status(thm)], ['100', '108', '117', '127'])).
% 3.81/4.03  thf('129', plain,
% 3.81/4.03      ((((k9_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03          = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 3.81/4.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('simplify', [status(thm)], ['128'])).
% 3.81/4.03  thf('130', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_1))),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('131', plain,
% 3.81/4.03      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 3.81/4.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('demod', [status(thm)], ['4', '5'])).
% 3.81/4.03  thf(t110_tmap_1, axiom,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.81/4.03       ( ![B:$i]:
% 3.81/4.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.81/4.03           ( ![C:$i]:
% 3.81/4.03             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.81/4.03               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 3.81/4.03                 ( ![D:$i]:
% 3.81/4.03                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 3.81/4.03                     ( r1_tmap_1 @
% 3.81/4.03                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 3.81/4.03                       ( k2_tmap_1 @
% 3.81/4.03                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 3.81/4.03                       D ) ) ) ) ) ) ) ) ))).
% 3.81/4.03  thf('132', plain,
% 3.81/4.03      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 3.81/4.03         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.81/4.03          | ((u1_struct_0 @ X39) != (X37))
% 3.81/4.03          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 3.81/4.03          | (r1_tmap_1 @ X39 @ (k6_tmap_1 @ X38 @ X37) @ 
% 3.81/4.03             (k2_tmap_1 @ X38 @ (k6_tmap_1 @ X38 @ X37) @ 
% 3.81/4.03              (k7_tmap_1 @ X38 @ X37) @ X39) @ 
% 3.81/4.03             X40)
% 3.81/4.03          | ~ (m1_pre_topc @ X39 @ X38)
% 3.81/4.03          | (v2_struct_0 @ X39)
% 3.81/4.03          | ~ (l1_pre_topc @ X38)
% 3.81/4.03          | ~ (v2_pre_topc @ X38)
% 3.81/4.03          | (v2_struct_0 @ X38))),
% 3.81/4.03      inference('cnf', [status(esa)], [t110_tmap_1])).
% 3.81/4.03  thf('133', plain,
% 3.81/4.03      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.81/4.03         ((v2_struct_0 @ X38)
% 3.81/4.03          | ~ (v2_pre_topc @ X38)
% 3.81/4.03          | ~ (l1_pre_topc @ X38)
% 3.81/4.03          | (v2_struct_0 @ X39)
% 3.81/4.03          | ~ (m1_pre_topc @ X39 @ X38)
% 3.81/4.03          | (r1_tmap_1 @ X39 @ (k6_tmap_1 @ X38 @ (u1_struct_0 @ X39)) @ 
% 3.81/4.03             (k2_tmap_1 @ X38 @ (k6_tmap_1 @ X38 @ (u1_struct_0 @ X39)) @ 
% 3.81/4.03              (k7_tmap_1 @ X38 @ (u1_struct_0 @ X39)) @ X39) @ 
% 3.81/4.03             X40)
% 3.81/4.03          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 3.81/4.03          | ~ (m1_subset_1 @ (u1_struct_0 @ X39) @ 
% 3.81/4.03               (k1_zfmisc_1 @ (u1_struct_0 @ X38))))),
% 3.81/4.03      inference('simplify', [status(thm)], ['132'])).
% 3.81/4.03  thf('134', plain,
% 3.81/4.03      (![X0 : $i]:
% 3.81/4.03         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 3.81/4.03          | (r1_tmap_1 @ sk_B_1 @ 
% 3.81/4.03             (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 3.81/4.03              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1) @ 
% 3.81/4.03             X0)
% 3.81/4.03          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 3.81/4.03          | (v2_struct_0 @ sk_B_1)
% 3.81/4.03          | ~ (l1_pre_topc @ sk_A)
% 3.81/4.03          | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03          | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['131', '133'])).
% 3.81/4.03  thf('135', plain,
% 3.81/4.03      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 3.81/4.03      inference('clc', [status(thm)], ['48', '49'])).
% 3.81/4.03  thf('136', plain,
% 3.81/4.03      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 3.81/4.03         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 3.81/4.03      inference('clc', [status(thm)], ['48', '49'])).
% 3.81/4.03  thf('137', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('140', plain,
% 3.81/4.03      (![X0 : $i]:
% 3.81/4.03         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 3.81/4.03          | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1) @ 
% 3.81/4.03             X0)
% 3.81/4.03          | (v2_struct_0 @ sk_B_1)
% 3.81/4.03          | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)],
% 3.81/4.03                ['134', '135', '136', '137', '138', '139'])).
% 3.81/4.03  thf('141', plain,
% 3.81/4.03      (((v2_struct_0 @ sk_A)
% 3.81/4.03        | (v2_struct_0 @ sk_B_1)
% 3.81/4.03        | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1) @ 
% 3.81/4.03           sk_C_1))),
% 3.81/4.03      inference('sup-', [status(thm)], ['130', '140'])).
% 3.81/4.03  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('143', plain,
% 3.81/4.03      (((r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1) @ 
% 3.81/4.03         sk_C_1)
% 3.81/4.03        | (v2_struct_0 @ sk_B_1))),
% 3.81/4.03      inference('clc', [status(thm)], ['141', '142'])).
% 3.81/4.03  thf('144', plain, (~ (v2_struct_0 @ sk_B_1)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('145', plain,
% 3.81/4.03      ((r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1) @ 
% 3.81/4.03        sk_C_1)),
% 3.81/4.03      inference('clc', [status(thm)], ['143', '144'])).
% 3.81/4.03  thf('146', plain,
% 3.81/4.03      (((r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 3.81/4.03         sk_C_1)
% 3.81/4.03        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 3.81/4.03      inference('sup+', [status(thm)], ['129', '145'])).
% 3.81/4.03  thf('147', plain,
% 3.81/4.03      (~ (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03           (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 3.81/4.03          sk_C_1)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('148', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 3.81/4.03      inference('clc', [status(thm)], ['146', '147'])).
% 3.81/4.03  thf('149', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1))),
% 3.81/4.03      inference('demod', [status(thm)], ['8', '148'])).
% 3.81/4.03  thf('150', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 3.81/4.03      inference('sup-', [status(thm)], ['1', '149'])).
% 3.81/4.03  thf(t3_xboole_0, axiom,
% 3.81/4.03    (![A:$i,B:$i]:
% 3.81/4.03     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.81/4.03            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.81/4.03       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.81/4.03            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.81/4.03  thf('151', plain,
% 3.81/4.03      (![X3 : $i, X4 : $i]:
% 3.81/4.03         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 3.81/4.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.81/4.03  thf('152', plain,
% 3.81/4.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.81/4.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.81/4.03  thf('153', plain,
% 3.81/4.03      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.81/4.03      inference('sup-', [status(thm)], ['151', '152'])).
% 3.81/4.03  thf(d3_tsep_1, axiom,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( l1_struct_0 @ A ) =>
% 3.81/4.03       ( ![B:$i]:
% 3.81/4.03         ( ( l1_struct_0 @ B ) =>
% 3.81/4.03           ( ( r1_tsep_1 @ A @ B ) <=>
% 3.81/4.03             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 3.81/4.03  thf('154', plain,
% 3.81/4.03      (![X27 : $i, X28 : $i]:
% 3.81/4.03         (~ (l1_struct_0 @ X27)
% 3.81/4.03          | ~ (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 3.81/4.03          | (r1_tsep_1 @ X28 @ X27)
% 3.81/4.03          | ~ (l1_struct_0 @ X28))),
% 3.81/4.03      inference('cnf', [status(esa)], [d3_tsep_1])).
% 3.81/4.03  thf('155', plain,
% 3.81/4.03      (![X0 : $i, X1 : $i]:
% 3.81/4.03         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.81/4.03          | ~ (l1_struct_0 @ X1)
% 3.81/4.03          | (r1_tsep_1 @ X1 @ X0)
% 3.81/4.03          | ~ (l1_struct_0 @ X0))),
% 3.81/4.03      inference('sup-', [status(thm)], ['153', '154'])).
% 3.81/4.03  thf('156', plain,
% 3.81/4.03      (![X0 : $i]:
% 3.81/4.03         (~ (l1_struct_0 @ sk_B_1)
% 3.81/4.03          | (r1_tsep_1 @ X0 @ sk_B_1)
% 3.81/4.03          | ~ (l1_struct_0 @ X0))),
% 3.81/4.03      inference('sup-', [status(thm)], ['150', '155'])).
% 3.81/4.03  thf('157', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf(dt_m1_pre_topc, axiom,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( l1_pre_topc @ A ) =>
% 3.81/4.03       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 3.81/4.03  thf('158', plain,
% 3.81/4.03      (![X11 : $i, X12 : $i]:
% 3.81/4.03         (~ (m1_pre_topc @ X11 @ X12)
% 3.81/4.03          | (l1_pre_topc @ X11)
% 3.81/4.03          | ~ (l1_pre_topc @ X12))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.81/4.03  thf('159', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 3.81/4.03      inference('sup-', [status(thm)], ['157', '158'])).
% 3.81/4.03  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('161', plain, ((l1_pre_topc @ sk_B_1)),
% 3.81/4.03      inference('demod', [status(thm)], ['159', '160'])).
% 3.81/4.03  thf(dt_l1_pre_topc, axiom,
% 3.81/4.03    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.81/4.03  thf('162', plain,
% 3.81/4.03      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 3.81/4.03      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.81/4.03  thf('163', plain, ((l1_struct_0 @ sk_B_1)),
% 3.81/4.03      inference('sup-', [status(thm)], ['161', '162'])).
% 3.81/4.03  thf('164', plain,
% 3.81/4.03      (![X0 : $i]: ((r1_tsep_1 @ X0 @ sk_B_1) | ~ (l1_struct_0 @ X0))),
% 3.81/4.03      inference('demod', [status(thm)], ['156', '163'])).
% 3.81/4.03  thf('165', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('166', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('167', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B_1))),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf(t118_tmap_1, axiom,
% 3.81/4.03    (![A:$i]:
% 3.81/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.81/4.03       ( ![B:$i]:
% 3.81/4.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.81/4.03           ( ![C:$i]:
% 3.81/4.03             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.81/4.03               ( ( r1_tsep_1 @ B @ C ) =>
% 3.81/4.03                 ( ![D:$i]:
% 3.81/4.03                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 3.81/4.03                     ( r1_tmap_1 @
% 3.81/4.03                       C @ ( k8_tmap_1 @ A @ B ) @ 
% 3.81/4.03                       ( k2_tmap_1 @
% 3.81/4.03                         A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 3.81/4.03                       D ) ) ) ) ) ) ) ) ))).
% 3.81/4.03  thf('168', plain,
% 3.81/4.03      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.81/4.03         ((v2_struct_0 @ X41)
% 3.81/4.03          | ~ (m1_pre_topc @ X41 @ X42)
% 3.81/4.03          | ~ (r1_tsep_1 @ X41 @ X43)
% 3.81/4.03          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X43))
% 3.81/4.03          | (r1_tmap_1 @ X43 @ (k8_tmap_1 @ X42 @ X41) @ 
% 3.81/4.03             (k2_tmap_1 @ X42 @ (k8_tmap_1 @ X42 @ X41) @ 
% 3.81/4.03              (k9_tmap_1 @ X42 @ X41) @ X43) @ 
% 3.81/4.03             X44)
% 3.81/4.03          | ~ (m1_pre_topc @ X43 @ X42)
% 3.81/4.03          | (v2_struct_0 @ X43)
% 3.81/4.03          | ~ (l1_pre_topc @ X42)
% 3.81/4.03          | ~ (v2_pre_topc @ X42)
% 3.81/4.03          | (v2_struct_0 @ X42))),
% 3.81/4.03      inference('cnf', [status(esa)], [t118_tmap_1])).
% 3.81/4.03  thf('169', plain,
% 3.81/4.03      (![X0 : $i, X1 : $i]:
% 3.81/4.03         ((v2_struct_0 @ X0)
% 3.81/4.03          | ~ (v2_pre_topc @ X0)
% 3.81/4.03          | ~ (l1_pre_topc @ X0)
% 3.81/4.03          | (v2_struct_0 @ sk_B_1)
% 3.81/4.03          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 3.81/4.03          | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ X0 @ X1) @ 
% 3.81/4.03             (k2_tmap_1 @ X0 @ (k8_tmap_1 @ X0 @ X1) @ (k9_tmap_1 @ X0 @ X1) @ 
% 3.81/4.03              sk_B_1) @ 
% 3.81/4.03             sk_C_1)
% 3.81/4.03          | ~ (r1_tsep_1 @ X1 @ sk_B_1)
% 3.81/4.03          | ~ (m1_pre_topc @ X1 @ X0)
% 3.81/4.03          | (v2_struct_0 @ X1))),
% 3.81/4.03      inference('sup-', [status(thm)], ['167', '168'])).
% 3.81/4.03  thf('170', plain,
% 3.81/4.03      (![X0 : $i]:
% 3.81/4.03         ((v2_struct_0 @ X0)
% 3.81/4.03          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.81/4.03          | ~ (r1_tsep_1 @ X0 @ sk_B_1)
% 3.81/4.03          | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ X0) @ 
% 3.81/4.03             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ X0) @ 
% 3.81/4.03              (k9_tmap_1 @ sk_A @ X0) @ sk_B_1) @ 
% 3.81/4.03             sk_C_1)
% 3.81/4.03          | (v2_struct_0 @ sk_B_1)
% 3.81/4.03          | ~ (l1_pre_topc @ sk_A)
% 3.81/4.03          | ~ (v2_pre_topc @ sk_A)
% 3.81/4.03          | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('sup-', [status(thm)], ['166', '169'])).
% 3.81/4.03  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('172', plain, ((v2_pre_topc @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('173', plain,
% 3.81/4.03      (![X0 : $i]:
% 3.81/4.03         ((v2_struct_0 @ X0)
% 3.81/4.03          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.81/4.03          | ~ (r1_tsep_1 @ X0 @ sk_B_1)
% 3.81/4.03          | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ X0) @ 
% 3.81/4.03             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ X0) @ 
% 3.81/4.03              (k9_tmap_1 @ sk_A @ X0) @ sk_B_1) @ 
% 3.81/4.03             sk_C_1)
% 3.81/4.03          | (v2_struct_0 @ sk_B_1)
% 3.81/4.03          | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('demod', [status(thm)], ['170', '171', '172'])).
% 3.81/4.03  thf('174', plain,
% 3.81/4.03      (((v2_struct_0 @ sk_A)
% 3.81/4.03        | (v2_struct_0 @ sk_B_1)
% 3.81/4.03        | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03            (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 3.81/4.03           sk_C_1)
% 3.81/4.03        | ~ (r1_tsep_1 @ sk_B_1 @ sk_B_1)
% 3.81/4.03        | (v2_struct_0 @ sk_B_1))),
% 3.81/4.03      inference('sup-', [status(thm)], ['165', '173'])).
% 3.81/4.03  thf('175', plain,
% 3.81/4.03      ((~ (r1_tsep_1 @ sk_B_1 @ sk_B_1)
% 3.81/4.03        | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03            (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 3.81/4.03           sk_C_1)
% 3.81/4.03        | (v2_struct_0 @ sk_B_1)
% 3.81/4.03        | (v2_struct_0 @ sk_A))),
% 3.81/4.03      inference('simplify', [status(thm)], ['174'])).
% 3.81/4.03  thf('176', plain,
% 3.81/4.03      ((~ (l1_struct_0 @ sk_B_1)
% 3.81/4.03        | (v2_struct_0 @ sk_A)
% 3.81/4.03        | (v2_struct_0 @ sk_B_1)
% 3.81/4.03        | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03            (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 3.81/4.03           sk_C_1))),
% 3.81/4.03      inference('sup-', [status(thm)], ['164', '175'])).
% 3.81/4.03  thf('177', plain, ((l1_struct_0 @ sk_B_1)),
% 3.81/4.03      inference('sup-', [status(thm)], ['161', '162'])).
% 3.81/4.03  thf('178', plain,
% 3.81/4.03      (((v2_struct_0 @ sk_A)
% 3.81/4.03        | (v2_struct_0 @ sk_B_1)
% 3.81/4.03        | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03            (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 3.81/4.03           sk_C_1))),
% 3.81/4.03      inference('demod', [status(thm)], ['176', '177'])).
% 3.81/4.03  thf('179', plain, (~ (v2_struct_0 @ sk_A)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('180', plain,
% 3.81/4.03      (((r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 3.81/4.03         sk_C_1)
% 3.81/4.03        | (v2_struct_0 @ sk_B_1))),
% 3.81/4.03      inference('clc', [status(thm)], ['178', '179'])).
% 3.81/4.03  thf('181', plain,
% 3.81/4.03      (~ (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.03           (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 3.81/4.03          sk_C_1)),
% 3.81/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.03  thf('182', plain, ((v2_struct_0 @ sk_B_1)),
% 3.81/4.03      inference('clc', [status(thm)], ['180', '181'])).
% 3.81/4.03  thf('183', plain, ($false), inference('demod', [status(thm)], ['0', '182'])).
% 3.81/4.03  
% 3.81/4.03  % SZS output end Refutation
% 3.81/4.03  
% 3.81/4.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
