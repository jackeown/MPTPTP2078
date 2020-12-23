%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1802+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JcrNqFigm0

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:17 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 870 expanded)
%              Number of leaves         :   41 ( 268 expanded)
%              Depth                    :   23
%              Number of atoms          : 2080 (18496 expanded)
%              Number of equality atoms :   30 (  80 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(t118_tmap_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                     => ( r1_tmap_1 @ C @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t118_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tsep_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X31 )
      | ( r1_tsep_1 @ X31 @ X30 )
      | ~ ( r1_tsep_1 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
    | ~ ( l1_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tsep_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['4','11','18'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_struct_0 @ X8 )
      | ~ ( r1_tsep_1 @ X9 @ X8 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('21',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('24',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_pre_topc @ X36 @ X37 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t109_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X34 ) @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( r1_tmap_1 @ X34 @ ( k6_tmap_1 @ X33 @ X32 ) @ ( k2_tmap_1 @ X33 @ ( k6_tmap_1 @ X33 @ X32 ) @ ( k7_tmap_1 @ X33 @ X32 ) @ X34 ) @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t109_tmap_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

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

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( X2
       != ( k8_tmap_1 @ X1 @ X0 ) )
      | ( X3
       != ( u1_struct_0 @ X0 ) )
      | ( X2
        = ( k6_tmap_1 @ X1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( ( k8_tmap_1 @ X1 @ X0 )
        = ( k6_tmap_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('44',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('52',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('60',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','49','57','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','68','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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

thf('72',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X14 @ X15 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('73',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
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
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

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

thf('79',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( X6
       != ( k9_tmap_1 @ X5 @ X4 ) )
      | ( X7
       != ( u1_struct_0 @ X4 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X5 @ X4 ) ) @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X5 @ X7 ) ) @ X6 @ ( k7_tmap_1 @ X5 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X5 @ X4 ) ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X5 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X5 @ X4 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X5 @ X4 ) @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X5 @ X4 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X5 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X5 @ X4 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X5 @ X4 ) ) @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X5 @ ( u1_struct_0 @ X4 ) ) ) @ ( k9_tmap_1 @ X5 @ X4 ) @ ( k7_tmap_1 @ X5 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_pre_topc @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('84',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('85',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('87',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('95',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84','92','100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

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

thf('107',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ( X24 = X28 )
      | ~ ( r1_funct_2 @ X25 @ X26 @ X29 @ X27 @ X24 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('110',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('114',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('115',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('122',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('123',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('131',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X10 @ X11 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('132',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','120','129','138'])).

thf('140',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('141',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('142',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('144',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('145',plain,(
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['142','145'])).

thf('147',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(fc4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) )
        & ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('148',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_tmap_1])).

thf('149',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k9_tmap_1 @ sk_A @ sk_B )
    = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['146','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','158'])).

thf('160',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_D_2 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    $false ),
    inference(demod,[status(thm)],['0','166'])).


%------------------------------------------------------------------------------
