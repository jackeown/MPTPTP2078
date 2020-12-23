%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1126+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fWMDttw3Nn

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:05 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 837 expanded)
%              Number of leaves         :   48 ( 267 expanded)
%              Depth                    :   24
%              Number of atoms          : 1904 (19648 expanded)
%              Number of equality atoms :   71 ( 432 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) @ X9 @ ( sk_D @ X9 @ X8 @ X10 ) ) @ X10 )
      | ( v5_pre_topc @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X8 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v5_pre_topc @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( v4_pre_topc @ X36 @ X34 )
      | ( m1_subset_1 @ ( sk_D_1 @ X36 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ( v4_pre_topc @ ( sk_D @ X9 @ X8 @ X10 ) @ X8 )
      | ( v5_pre_topc @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v5_pre_topc @ X9 @ X10 @ X8 )
      | ~ ( v4_pre_topc @ X11 @ X8 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) @ X9 @ X11 ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( v4_pre_topc @ X36 @ X34 )
      | ( v4_pre_topc @ ( sk_D_1 @ X36 @ X34 @ X35 ) @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('74',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k9_subset_1 @ X25 @ X23 @ X24 )
        = ( k3_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('79',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( v4_pre_topc @ X36 @ X34 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X34 ) @ ( sk_D_1 @ X36 @ X34 @ X35 ) @ ( k2_struct_0 @ X34 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ X0 ) @ ( k2_struct_0 @ sk_D_2 ) )
        = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v4_pre_topc @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 ),
    inference(clc,[status(thm)],['43','44'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ X0 ) @ ( k2_struct_0 @ sk_D_2 ) )
        = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ sk_D_2 ) )
      = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ sk_D_2 ) )
    = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k3_xboole_0 @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ sk_D_2 ) )
      = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['76','85'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('87',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X6 )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('89',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('90',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) )
    = ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','90'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('92',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('94',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v5_relat_1 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('95',plain,(
    v5_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('96',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['97','100'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('102',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_xboole_0 @ X32 @ X33 )
        = X32 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('103',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_2 ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('104',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ X29 @ X30 )
        = ( k10_relat_1 @ X29 @ ( k3_xboole_0 @ ( k2_relat_1 @ X29 ) @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('105',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D_2 ) )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('107',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D_2 ) )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('108',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v5_relat_1 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    v5_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('115',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_xboole_0 @ X32 @ X33 )
        = X32 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('117',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('119',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X26 @ X27 ) @ ( k10_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['117','121'])).

thf('123',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('124',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ X29 @ X30 )
        = ( k10_relat_1 @ X29 @ ( k3_xboole_0 @ ( k2_relat_1 @ X29 ) @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('125',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('127',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['122','127','128','129'])).

thf('131',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['108','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('133',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D_2 ) )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['107','133'])).

thf('135',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('136',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('137',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D_2 ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','139'])).

thf('141',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X26 @ X27 ) @ ( k10_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ X29 @ X30 )
        = ( k10_relat_1 @ X29 @ ( k3_xboole_0 @ ( k2_relat_1 @ X29 ) @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('147',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('148',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('149',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X26 @ X27 ) @ ( k10_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ X0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['146','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['145','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ X0 ) )
        = ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['92','158'])).

thf('160',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) )
    = ( k10_relat_1 @ sk_C @ ( sk_D_1 @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['91','161'])).

thf('163',plain,(
    v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_D_2 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['73','162'])).

thf('164',plain,(
    $false ),
    inference(demod,[status(thm)],['22','163'])).


%------------------------------------------------------------------------------
