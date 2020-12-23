%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1126+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Lu0Y8xiqqp

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:05 EST 2020

% Result     : Theorem 24.62s
% Output     : Refutation 24.62s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 515 expanded)
%              Number of leaves         :   46 ( 168 expanded)
%              Depth                    :   20
%              Number of atoms          : 1647 (13829 expanded)
%              Number of equality atoms :   48 ( 270 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t57_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
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
                  ( ( m1_pre_topc @ D @ B )
                 => ( ( v5_pre_topc @ C @ A @ B )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) ) ) ) )
                       => ( ( E = C )
                         => ( v5_pre_topc @ E @ A @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
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
                    ( ( m1_pre_topc @ D @ B )
                   => ( ( v5_pre_topc @ C @ A @ B )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) ) ) ) )
                         => ( ( E = C )
                           => ( v5_pre_topc @ E @ A @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_pre_topc])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_E = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d12_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( v4_pre_topc @ D @ B )
                     => ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ ( sk_D @ X6 @ X5 @ X7 ) ) @ X7 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('6',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_E = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('13',plain,(
    m1_pre_topc @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','7','8','11','12','17'])).

thf('19',plain,(
    ~ ( v5_pre_topc @ sk_E @ sk_A @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_E = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['18','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('30',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('31',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('33',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(t43_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v4_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v4_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( v4_pre_topc @ X39 @ X37 )
      | ( m1_subset_1 @ ( sk_D_1 @ X39 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v4_pre_topc @ ( sk_D @ X6 @ X5 @ X7 ) @ X5 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_D_2 )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('42',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('43',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_D_2 )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_D_2 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('45',plain,(
    v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,
    ( ~ ( v4_pre_topc @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ sk_B )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('66',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( v4_pre_topc @ X39 @ X37 )
      | ( v4_pre_topc @ ( sk_D_1 @ X39 @ X37 @ X38 ) @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 ),
    inference(clc,[status(thm)],['43','44'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v4_pre_topc @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_pre_topc @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['63','72'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('74',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k10_relat_1 @ X30 @ X31 )
        = ( k10_relat_1 @ X30 @ ( k3_xboole_0 @ ( k2_relat_1 @ X30 ) @ X31 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('75',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('76',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k9_subset_1 @ X26 @ X24 @ X25 )
        = ( k3_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('80',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( v4_pre_topc @ X39 @ X37 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X37 ) @ ( sk_D_1 @ X39 @ X37 @ X38 ) @ ( k2_struct_0 @ X37 ) )
        = X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ X0 ) @ ( k2_struct_0 @ sk_D_2 ) )
        = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 ),
    inference(clc,[status(thm)],['43','44'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ X0 ) @ ( k2_struct_0 @ sk_D_2 ) )
        = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ sk_D_2 ) )
      = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ sk_D_2 ) )
    = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k3_xboole_0 @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ sk_D_2 ) )
      = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['77','86'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('88',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X3 )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('89',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('90',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('91',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) )
    = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','91'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('93',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('94',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k3_xboole_0 @ X28 @ X29 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X27 @ X28 ) @ ( k10_relat_1 @ X27 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('96',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('97',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('99',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('100',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['97','100'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('102',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('104',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_xboole_0 @ X32 @ X33 )
        = X32 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('105',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_2 ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k10_relat_1 @ X30 @ X31 )
        = ( k10_relat_1 @ X30 @ ( k3_xboole_0 @ ( k2_relat_1 @ X30 ) @ X31 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('107',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D_2 ) )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D_2 ) )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k3_xboole_0 @ X28 @ X29 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X27 @ X28 ) @ ( k10_relat_1 @ X27 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['108','109'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ X0 ) )
        = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['94','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['108','109'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ X0 ) )
        = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['93','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
    = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['92','123'])).

thf('125',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['74','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['108','109'])).

thf('127',plain,
    ( ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
    = ( k10_relat_1 @ sk_C @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['73','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['22','128'])).


%------------------------------------------------------------------------------
