%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bbFErPe3y2

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:07 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  350 (8122 expanded)
%              Number of leaves         :   36 (2430 expanded)
%              Depth                    :   29
%              Number of atoms          : 4613 (568686 expanded)
%              Number of equality atoms :   80 (5145 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t132_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                          & ( r4_tsep_1 @ A @ D @ E ) )
                       => ( ( ( v1_funct_1 @ C )
                            & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ C @ A @ B )
                            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( A
                              = ( k1_tsep_1 @ A @ D @ E ) )
                            & ( r4_tsep_1 @ A @ D @ E ) )
                         => ( ( ( v1_funct_1 @ C )
                              & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ C @ A @ B )
                              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                          <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                              & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( ( k2_tmap_1 @ X17 @ X15 @ X18 @ X16 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) @ X18 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k2_partfun1 @ X9 @ X10 @ X8 @ X11 )
        = ( k7_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t129_tmap_1,axiom,(
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
                 => ( ( r4_tsep_1 @ A @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X27 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X27 ) @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X27 ) @ X27 @ X23 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X24 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X24 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X24 ) @ X24 @ X23 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( r4_tsep_1 @ X25 @ X27 @ X24 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','37','40','41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['31','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('60',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('61',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('75',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['75'])).

thf('77',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['62','76'])).

thf('78',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('79',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('81',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('86',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['81','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('92',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','52','53','54','55','56','57','58','59','60','79','80','92','93','94'])).

thf('96',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('99',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','37','40','41','42'])).

thf('105',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) @ X23 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X24 ) @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( r4_tsep_1 @ X25 @ X27 @ X24 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E ) @ sk_E @ X0 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E ) @ sk_E @ X0 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','121','122','123','124','125','126','127'])).

thf('129',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_E ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('131',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('132',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('134',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('136',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('139',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('140',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('144',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('155',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('158',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('159',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('160',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('161',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('162',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('164',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','131','132','133','151','152','153','154','155','156','157','158','159','160','161','162','163','164','165','166'])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['101','167'])).

thf('169',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('170',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['71'])).

thf('171',plain,
    ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['100'])).

thf('182',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','37','40','41','42'])).

thf('184',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) @ X23 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X25 @ X27 @ X24 ) ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X25 @ X23 @ X26 @ X27 ) @ X27 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( r4_tsep_1 @ X25 @ X27 @ X24 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X1 @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X1 @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['185','186','187','188','189','190','191','192'])).

thf('194',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['182','193'])).

thf('195',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('196',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('204',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('206',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['194','195','196','197','198','199','200','201','202','203','204','205','206','207','208','209'])).

thf('211',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['181','210'])).

thf('212',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('213',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['213'])).

thf('215',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup+',[status(thm)],['212','214'])).

thf('216',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('218',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','37','40','41','42'])).

thf('220',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['218','219'])).

thf('221',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('223',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_E ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('227',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['220','227'])).

thf('229',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('230',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('231',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('234',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['71'])).

thf('235',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['225','226'])).

thf('237',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['237'])).

thf('239',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['232','238'])).

thf('240',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('241',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('243',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('246',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['71'])).

thf('247',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['225','226'])).

thf('249',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['249'])).

thf('251',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['244','250'])).

thf('252',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('253',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('255',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','51'])).

thf('256',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('257',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('258',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('259',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('260',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('261',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['216','217','228','229','230','241','242','253','254','255','256','257','258','259','260','261','262','263'])).

thf('265',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['215','264'])).

thf('266',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['211','265'])).

thf('267',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['100'])).

thf('268',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['272','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['277'])).

thf('279',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference('sat_resolution*',[status(thm)],['180','276','278'])).

thf('280',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ),
    inference(simpl_trail,[status(thm)],['99','279'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','280'])).

thf('282',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','281'])).

thf('283',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['220','227'])).

thf('284',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('286',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('287',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('288',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('289',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('290',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['213'])).

thf('291',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('292',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['290','291'])).

thf('293',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['293'])).

thf('295',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference('sat_resolution*',[status(thm)],['180','276','294'])).

thf('296',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ),
    inference(simpl_trail,[status(thm)],['292','295'])).

thf('297',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['149','150'])).

thf('299',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['282','283','284','285','286','287','288','289','296','297','298','299','300'])).

thf('302',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['71'])).

thf('303',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['180','276'])).

thf('304',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['302','303'])).

thf('305',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['301','304'])).

thf('306',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['307','308'])).

thf('310',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['309','310'])).

thf('312',plain,(
    $false ),
    inference(demod,[status(thm)],['0','311'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bbFErPe3y2
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.94  % Solved by: fo/fo7.sh
% 0.76/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.94  % done 779 iterations in 0.480s
% 0.76/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.94  % SZS output start Refutation
% 0.76/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.94  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.76/0.94  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.76/0.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.94  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.76/0.94  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.76/0.94  thf(sk_E_type, type, sk_E: $i).
% 0.76/0.94  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.94  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.94  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.76/0.94  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.76/0.94  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.94  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.94  thf(t132_tmap_1, conjecture,
% 0.76/0.94    (![A:$i]:
% 0.76/0.94     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.94       ( ![B:$i]:
% 0.76/0.94         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.94             ( l1_pre_topc @ B ) ) =>
% 0.76/0.94           ( ![C:$i]:
% 0.76/0.94             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.94                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.94                 ( m1_subset_1 @
% 0.76/0.94                   C @ 
% 0.76/0.94                   ( k1_zfmisc_1 @
% 0.76/0.94                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.94               ( ![D:$i]:
% 0.76/0.94                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.94                   ( ![E:$i]:
% 0.76/0.94                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.76/0.94                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 0.76/0.94                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 0.76/0.94                         ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.94                             ( v1_funct_2 @
% 0.76/0.94                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.94                             ( v5_pre_topc @ C @ A @ B ) & 
% 0.76/0.94                             ( m1_subset_1 @
% 0.76/0.94                               C @ 
% 0.76/0.94                               ( k1_zfmisc_1 @
% 0.76/0.94                                 ( k2_zfmisc_1 @
% 0.76/0.94                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.76/0.94                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.76/0.94                             ( v1_funct_2 @
% 0.76/0.94                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.76/0.94                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.94                             ( v5_pre_topc @
% 0.76/0.94                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.76/0.94                             ( m1_subset_1 @
% 0.76/0.94                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.76/0.94                               ( k1_zfmisc_1 @
% 0.76/0.94                                 ( k2_zfmisc_1 @
% 0.76/0.94                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.76/0.94                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.76/0.94                             ( v1_funct_2 @
% 0.76/0.94                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.76/0.94                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.94                             ( v5_pre_topc @
% 0.76/0.94                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.76/0.94                             ( m1_subset_1 @
% 0.76/0.94                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.76/0.94                               ( k1_zfmisc_1 @
% 0.76/0.94                                 ( k2_zfmisc_1 @
% 0.76/0.94                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.94    (~( ![A:$i]:
% 0.76/0.94        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.76/0.94            ( l1_pre_topc @ A ) ) =>
% 0.76/0.94          ( ![B:$i]:
% 0.76/0.94            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.94                ( l1_pre_topc @ B ) ) =>
% 0.76/0.94              ( ![C:$i]:
% 0.76/0.94                ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.94                    ( v1_funct_2 @
% 0.76/0.94                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.94                    ( m1_subset_1 @
% 0.76/0.94                      C @ 
% 0.76/0.94                      ( k1_zfmisc_1 @
% 0.76/0.94                        ( k2_zfmisc_1 @
% 0.76/0.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.94                  ( ![D:$i]:
% 0.76/0.94                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.94                      ( ![E:$i]:
% 0.76/0.94                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.76/0.94                          ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 0.76/0.94                              ( r4_tsep_1 @ A @ D @ E ) ) =>
% 0.76/0.94                            ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.94                                ( v1_funct_2 @
% 0.76/0.94                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.94                                ( v5_pre_topc @ C @ A @ B ) & 
% 0.76/0.94                                ( m1_subset_1 @
% 0.76/0.94                                  C @ 
% 0.76/0.94                                  ( k1_zfmisc_1 @
% 0.76/0.94                                    ( k2_zfmisc_1 @
% 0.76/0.94                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.76/0.94                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.76/0.94                                ( v1_funct_2 @
% 0.76/0.94                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.76/0.94                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.94                                ( v5_pre_topc @
% 0.76/0.94                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.76/0.95                                ( m1_subset_1 @
% 0.76/0.95                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.76/0.95                                  ( k1_zfmisc_1 @
% 0.76/0.95                                    ( k2_zfmisc_1 @
% 0.76/0.95                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.76/0.95                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.76/0.95                                ( v1_funct_2 @
% 0.76/0.95                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.76/0.95                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.95                                ( v5_pre_topc @
% 0.76/0.95                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.76/0.95                                ( m1_subset_1 @
% 0.76/0.95                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.76/0.95                                  ( k1_zfmisc_1 @
% 0.76/0.95                                    ( k2_zfmisc_1 @
% 0.76/0.95                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t132_tmap_1])).
% 0.76/0.95  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('2', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(d4_tmap_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.95       ( ![B:$i]:
% 0.76/0.95         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.95             ( l1_pre_topc @ B ) ) =>
% 0.76/0.95           ( ![C:$i]:
% 0.76/0.95             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.95                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.95                 ( m1_subset_1 @
% 0.76/0.95                   C @ 
% 0.76/0.95                   ( k1_zfmisc_1 @
% 0.76/0.95                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.95               ( ![D:$i]:
% 0.76/0.95                 ( ( m1_pre_topc @ D @ A ) =>
% 0.76/0.95                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.76/0.95                     ( k2_partfun1 @
% 0.76/0.95                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.76/0.95                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.95  thf('3', plain,
% 0.76/0.95      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.95         ((v2_struct_0 @ X15)
% 0.76/0.95          | ~ (v2_pre_topc @ X15)
% 0.76/0.95          | ~ (l1_pre_topc @ X15)
% 0.76/0.95          | ~ (m1_pre_topc @ X16 @ X17)
% 0.76/0.95          | ((k2_tmap_1 @ X17 @ X15 @ X18 @ X16)
% 0.76/0.95              = (k2_partfun1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ 
% 0.76/0.95                 X18 @ (u1_struct_0 @ X16)))
% 0.76/0.95          | ~ (m1_subset_1 @ X18 @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 0.76/0.95          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 0.76/0.95          | ~ (v1_funct_1 @ X18)
% 0.76/0.95          | ~ (l1_pre_topc @ X17)
% 0.76/0.95          | ~ (v2_pre_topc @ X17)
% 0.76/0.95          | (v2_struct_0 @ X17))),
% 0.76/0.95      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.76/0.95  thf('4', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v2_struct_0 @ sk_A)
% 0.76/0.95          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.95          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.95          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.95          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.76/0.95              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.95                 sk_C @ (u1_struct_0 @ X0)))
% 0.76/0.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.95          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.95          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.95          | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('8', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('9', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(redefinition_k2_partfun1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.95     ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.76/0.95  thf('10', plain,
% 0.76/0.95      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.76/0.95          | ~ (v1_funct_1 @ X8)
% 0.76/0.95          | ((k2_partfun1 @ X9 @ X10 @ X8 @ X11) = (k7_relat_1 @ X8 @ X11)))),
% 0.76/0.95      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.76/0.95  thf('11', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.76/0.95            X0) = (k7_relat_1 @ sk_C @ X0))
% 0.76/0.95          | ~ (v1_funct_1 @ sk_C))),
% 0.76/0.95      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.95  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('13', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.76/0.95           X0) = (k7_relat_1 @ sk_C @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['11', '12'])).
% 0.76/0.95  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('16', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v2_struct_0 @ sk_A)
% 0.76/0.95          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.76/0.95              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 0.76/0.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 0.76/0.95  thf('17', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_B)
% 0.76/0.95        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 0.76/0.95        | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['1', '16'])).
% 0.76/0.95  thf('18', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('19', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_A)
% 0.76/0.95        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E))))),
% 0.76/0.95      inference('clc', [status(thm)], ['17', '18'])).
% 0.76/0.95  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('21', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('22', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('23', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v2_struct_0 @ sk_A)
% 0.76/0.95          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.76/0.95              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 0.76/0.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 0.76/0.95  thf('24', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_B)
% 0.76/0.95        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 0.76/0.95        | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.95  thf('25', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('26', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_A)
% 0.76/0.95        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D))))),
% 0.76/0.95      inference('clc', [status(thm)], ['24', '25'])).
% 0.76/0.95  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('28', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf(t129_tmap_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.95       ( ![B:$i]:
% 0.76/0.95         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.95             ( l1_pre_topc @ B ) ) =>
% 0.76/0.95           ( ![C:$i]:
% 0.76/0.95             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.95               ( ![D:$i]:
% 0.76/0.95                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.95                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 0.76/0.95                     ( ![E:$i]:
% 0.76/0.95                       ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.95                           ( v1_funct_2 @
% 0.76/0.95                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.95                           ( m1_subset_1 @
% 0.76/0.95                             E @ 
% 0.76/0.95                             ( k1_zfmisc_1 @
% 0.76/0.95                               ( k2_zfmisc_1 @
% 0.76/0.95                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.95                         ( ( ( v1_funct_1 @
% 0.76/0.95                               ( k2_tmap_1 @
% 0.76/0.95                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) ) & 
% 0.76/0.95                             ( v1_funct_2 @
% 0.76/0.95                               ( k2_tmap_1 @
% 0.76/0.95                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.95                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.95                               ( u1_struct_0 @ B ) ) & 
% 0.76/0.95                             ( v5_pre_topc @
% 0.76/0.95                               ( k2_tmap_1 @
% 0.76/0.95                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.95                               ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.76/0.95                             ( m1_subset_1 @
% 0.76/0.95                               ( k2_tmap_1 @
% 0.76/0.95                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.95                               ( k1_zfmisc_1 @
% 0.76/0.95                                 ( k2_zfmisc_1 @
% 0.76/0.95                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.95                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.76/0.95                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.76/0.95                             ( v1_funct_2 @
% 0.76/0.95                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 0.76/0.95                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.95                             ( v5_pre_topc @
% 0.76/0.95                               ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B ) & 
% 0.76/0.95                             ( m1_subset_1 @
% 0.76/0.95                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 0.76/0.95                               ( k1_zfmisc_1 @
% 0.76/0.95                                 ( k2_zfmisc_1 @
% 0.76/0.95                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.76/0.95                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) ) & 
% 0.76/0.95                             ( v1_funct_2 @
% 0.76/0.95                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 0.76/0.95                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.95                             ( v5_pre_topc @
% 0.76/0.95                               ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B ) & 
% 0.76/0.95                             ( m1_subset_1 @
% 0.76/0.95                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 0.76/0.95                               ( k1_zfmisc_1 @
% 0.76/0.95                                 ( k2_zfmisc_1 @
% 0.76/0.95                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.95  thf('29', plain,
% 0.76/0.95      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.95         ((v2_struct_0 @ X23)
% 0.76/0.95          | ~ (v2_pre_topc @ X23)
% 0.76/0.95          | ~ (l1_pre_topc @ X23)
% 0.76/0.95          | (v2_struct_0 @ X24)
% 0.76/0.95          | ~ (m1_pre_topc @ X24 @ X25)
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X27))
% 0.76/0.95          | ~ (v1_funct_2 @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X27) @ 
% 0.76/0.95               (u1_struct_0 @ X27) @ (u1_struct_0 @ X23))
% 0.76/0.95          | ~ (v5_pre_topc @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X27) @ X27 @ X23)
% 0.76/0.95          | ~ (m1_subset_1 @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X27) @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X23))))
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X24))
% 0.76/0.95          | ~ (v1_funct_2 @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X24) @ 
% 0.76/0.95               (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.76/0.95          | ~ (v5_pre_topc @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X24) @ X24 @ X23)
% 0.76/0.95          | ~ (m1_subset_1 @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X24) @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.76/0.95          | (v5_pre_topc @ 
% 0.76/0.95             (k2_tmap_1 @ X25 @ X23 @ X26 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95             (k1_tsep_1 @ X25 @ X27 @ X24) @ X23)
% 0.76/0.95          | ~ (m1_subset_1 @ X26 @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))))
% 0.76/0.95          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))
% 0.76/0.95          | ~ (v1_funct_1 @ X26)
% 0.76/0.95          | ~ (r4_tsep_1 @ X25 @ X27 @ X24)
% 0.76/0.95          | ~ (m1_pre_topc @ X27 @ X25)
% 0.76/0.95          | (v2_struct_0 @ X27)
% 0.76/0.95          | ~ (l1_pre_topc @ X25)
% 0.76/0.95          | ~ (v2_pre_topc @ X25)
% 0.76/0.95          | (v2_struct_0 @ X25))),
% 0.76/0.95      inference('cnf', [status(esa)], [t129_tmap_1])).
% 0.76/0.95  thf('30', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | (v2_struct_0 @ sk_A)
% 0.76/0.95          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.95          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ sk_D)
% 0.76/0.95          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.76/0.95          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.76/0.95          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.95          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (m1_subset_1 @ sk_C @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | (v5_pre_topc @ 
% 0.76/0.95             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.76/0.95             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 0.76/0.95          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.76/0.95          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.76/0.95               sk_B)
% 0.76/0.95          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.76/0.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ X0)
% 0.76/0.95          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.95          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.95          | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.95  thf('31', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('32', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(dt_k2_tmap_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.95     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.76/0.95         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.95         ( m1_subset_1 @
% 0.76/0.95           C @ 
% 0.76/0.95           ( k1_zfmisc_1 @
% 0.76/0.95             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.76/0.95         ( l1_struct_0 @ D ) ) =>
% 0.76/0.95       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.76/0.95         ( v1_funct_2 @
% 0.76/0.95           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.76/0.95           ( u1_struct_0 @ B ) ) & 
% 0.76/0.95         ( m1_subset_1 @
% 0.76/0.95           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.76/0.95           ( k1_zfmisc_1 @
% 0.76/0.95             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.76/0.95  thf('33', plain,
% 0.76/0.95      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X19 @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 0.76/0.95          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.76/0.95          | ~ (v1_funct_1 @ X19)
% 0.76/0.95          | ~ (l1_struct_0 @ X21)
% 0.76/0.95          | ~ (l1_struct_0 @ X20)
% 0.76/0.95          | ~ (l1_struct_0 @ X22)
% 0.76/0.95          | (m1_subset_1 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21)))))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.76/0.95  thf('34', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95           (k1_zfmisc_1 @ 
% 0.76/0.95            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X0)
% 0.76/0.95          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.95          | ~ (l1_struct_0 @ sk_B)
% 0.76/0.95          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.95          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['32', '33'])).
% 0.76/0.95  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(dt_l1_pre_topc, axiom,
% 0.76/0.95    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.76/0.95  thf('36', plain,
% 0.76/0.95      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.95  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.95      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.95  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('39', plain,
% 0.76/0.95      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.95  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.95  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('42', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('43', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95           (k1_zfmisc_1 @ 
% 0.76/0.95            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '37', '40', '41', '42'])).
% 0.76/0.95  thf('44', plain,
% 0.76/0.95      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 0.76/0.95         (k1_zfmisc_1 @ 
% 0.76/0.95          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | ~ (l1_struct_0 @ sk_D))),
% 0.76/0.95      inference('sup+', [status(thm)], ['31', '43'])).
% 0.76/0.95  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(dt_m1_pre_topc, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( l1_pre_topc @ A ) =>
% 0.76/0.95       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.76/0.95  thf('46', plain,
% 0.76/0.95      (![X13 : $i, X14 : $i]:
% 0.76/0.95         (~ (m1_pre_topc @ X13 @ X14)
% 0.76/0.95          | (l1_pre_topc @ X13)
% 0.76/0.95          | ~ (l1_pre_topc @ X14))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.76/0.95  thf('47', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.76/0.95      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.95  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('49', plain, ((l1_pre_topc @ sk_D)),
% 0.76/0.95      inference('demod', [status(thm)], ['47', '48'])).
% 0.76/0.95  thf('50', plain,
% 0.76/0.95      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.95  thf('51', plain, ((l1_struct_0 @ sk_D)),
% 0.76/0.95      inference('sup-', [status(thm)], ['49', '50'])).
% 0.76/0.95  thf('52', plain,
% 0.76/0.95      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('demod', [status(thm)], ['44', '51'])).
% 0.76/0.95  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('55', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('57', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('58', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('59', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('60', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('61', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | (v1_funct_1 @ sk_C))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('62', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.76/0.95         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('split', [status(esa)], ['61'])).
% 0.76/0.95  thf('63', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('64', plain,
% 0.76/0.95      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X19 @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 0.76/0.95          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.76/0.95          | ~ (v1_funct_1 @ X19)
% 0.76/0.95          | ~ (l1_struct_0 @ X21)
% 0.76/0.95          | ~ (l1_struct_0 @ X20)
% 0.76/0.95          | ~ (l1_struct_0 @ X22)
% 0.76/0.95          | (v1_funct_2 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22) @ 
% 0.76/0.95             (u1_struct_0 @ X22) @ (u1_struct_0 @ X21)))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.76/0.95  thf('65', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (l1_struct_0 @ X0)
% 0.76/0.95          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.95          | ~ (l1_struct_0 @ sk_B)
% 0.76/0.95          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.95          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['63', '64'])).
% 0.76/0.95  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.95      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.95  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.95  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('69', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('70', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.76/0.95  thf('71', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95           (k1_zfmisc_1 @ 
% 0.76/0.95            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95             sk_B)
% 0.76/0.95        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.76/0.95        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.76/0.95             sk_B)
% 0.76/0.95        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.76/0.95        | ~ (m1_subset_1 @ sk_C @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.76/0.95        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | ~ (v1_funct_1 @ sk_C))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('72', plain,
% 0.76/0.95      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('split', [status(esa)], ['71'])).
% 0.76/0.95  thf('73', plain,
% 0.76/0.95      ((~ (l1_struct_0 @ sk_D))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['70', '72'])).
% 0.76/0.95  thf('74', plain, ((l1_struct_0 @ sk_D)),
% 0.76/0.95      inference('sup-', [status(thm)], ['49', '50'])).
% 0.76/0.95  thf('75', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['73', '74'])).
% 0.76/0.95  thf('76', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)], ['75'])).
% 0.76/0.95  thf('77', plain,
% 0.76/0.95      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['62', '76'])).
% 0.76/0.95  thf('78', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('79', plain,
% 0.76/0.95      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 0.76/0.95        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['77', '78'])).
% 0.76/0.95  thf('80', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('81', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('82', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('83', plain,
% 0.76/0.95      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X19 @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 0.76/0.95          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.76/0.95          | ~ (v1_funct_1 @ X19)
% 0.76/0.95          | ~ (l1_struct_0 @ X21)
% 0.76/0.95          | ~ (l1_struct_0 @ X20)
% 0.76/0.95          | ~ (l1_struct_0 @ X22)
% 0.76/0.95          | (v1_funct_1 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22)))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.76/0.95  thf('84', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (l1_struct_0 @ X0)
% 0.76/0.95          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.95          | ~ (l1_struct_0 @ sk_B)
% 0.76/0.95          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.95          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['82', '83'])).
% 0.76/0.95  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.95      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.95  thf('86', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.95  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('88', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('89', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.76/0.95  thf('90', plain,
% 0.76/0.95      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 0.76/0.95        | ~ (l1_struct_0 @ sk_D))),
% 0.76/0.95      inference('sup+', [status(thm)], ['81', '89'])).
% 0.76/0.95  thf('91', plain, ((l1_struct_0 @ sk_D)),
% 0.76/0.95      inference('sup-', [status(thm)], ['49', '50'])).
% 0.76/0.95  thf('92', plain, ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('demod', [status(thm)], ['90', '91'])).
% 0.76/0.95  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('94', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('95', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v2_struct_0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ sk_D)
% 0.76/0.95          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.76/0.95          | (v5_pre_topc @ 
% 0.76/0.95             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.76/0.95             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 0.76/0.95          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.76/0.95          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 0.76/0.95               sk_D @ sk_B)
% 0.76/0.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ X0)
% 0.76/0.95          | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['30', '52', '53', '54', '55', '56', '57', '58', '59', '60', 
% 0.76/0.95                 '79', '80', '92', '93', '94'])).
% 0.76/0.95  thf('96', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.76/0.95        | (v1_funct_1 @ sk_C))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('97', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 0.76/0.95         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['96'])).
% 0.76/0.95  thf('98', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('99', plain,
% 0.76/0.95      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B))
% 0.76/0.95         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['97', '98'])).
% 0.76/0.95  thf('100', plain,
% 0.76/0.95      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.76/0.95        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('101', plain,
% 0.76/0.95      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.76/0.95         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['100'])).
% 0.76/0.95  thf('102', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.76/0.95  thf('103', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.76/0.95  thf('104', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95           (k1_zfmisc_1 @ 
% 0.76/0.95            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '37', '40', '41', '42'])).
% 0.76/0.95  thf('105', plain,
% 0.76/0.95      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X19 @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 0.76/0.95          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.76/0.95          | ~ (v1_funct_1 @ X19)
% 0.76/0.95          | ~ (l1_struct_0 @ X21)
% 0.76/0.95          | ~ (l1_struct_0 @ X20)
% 0.76/0.95          | ~ (l1_struct_0 @ X22)
% 0.76/0.95          | (m1_subset_1 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21)))))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.76/0.95  thf('106', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (l1_struct_0 @ X0)
% 0.76/0.95          | (m1_subset_1 @ 
% 0.76/0.95             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95              X1) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X1)
% 0.76/0.95          | ~ (l1_struct_0 @ X0)
% 0.76/0.95          | ~ (l1_struct_0 @ sk_B)
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['104', '105'])).
% 0.76/0.95  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.95  thf('108', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (l1_struct_0 @ X0)
% 0.76/0.95          | (m1_subset_1 @ 
% 0.76/0.95             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95              X1) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X1)
% 0.76/0.95          | ~ (l1_struct_0 @ X0)
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['106', '107'])).
% 0.76/0.95  thf('109', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (l1_struct_0 @ X1)
% 0.76/0.95          | (m1_subset_1 @ 
% 0.76/0.95             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95              X1) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('simplify', [status(thm)], ['108'])).
% 0.76/0.95  thf('110', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (l1_struct_0 @ X0)
% 0.76/0.95          | ~ (l1_struct_0 @ X0)
% 0.76/0.95          | (m1_subset_1 @ 
% 0.76/0.95             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95              X1) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X1)
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['103', '109'])).
% 0.76/0.95  thf('111', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (l1_struct_0 @ X1)
% 0.76/0.95          | (m1_subset_1 @ 
% 0.76/0.95             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95              X1) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('simplify', [status(thm)], ['110'])).
% 0.76/0.95  thf('112', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (l1_struct_0 @ X0)
% 0.76/0.95          | ~ (l1_struct_0 @ X0)
% 0.76/0.95          | (m1_subset_1 @ 
% 0.76/0.95             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95              X1) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['102', '111'])).
% 0.76/0.95  thf('113', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (l1_struct_0 @ X1)
% 0.76/0.95          | (m1_subset_1 @ 
% 0.76/0.95             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95              X1) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('simplify', [status(thm)], ['112'])).
% 0.76/0.95  thf('114', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('115', plain,
% 0.76/0.95      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.95         ((v2_struct_0 @ X23)
% 0.76/0.95          | ~ (v2_pre_topc @ X23)
% 0.76/0.95          | ~ (l1_pre_topc @ X23)
% 0.76/0.95          | (v2_struct_0 @ X24)
% 0.76/0.95          | ~ (m1_pre_topc @ X24 @ X25)
% 0.76/0.95          | ~ (v1_funct_1 @ 
% 0.76/0.95               (k2_tmap_1 @ X25 @ X23 @ X26 @ (k1_tsep_1 @ X25 @ X27 @ X24)))
% 0.76/0.95          | ~ (v1_funct_2 @ 
% 0.76/0.95               (k2_tmap_1 @ X25 @ X23 @ X26 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95               (u1_struct_0 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95               (u1_struct_0 @ X23))
% 0.76/0.95          | ~ (v5_pre_topc @ 
% 0.76/0.95               (k2_tmap_1 @ X25 @ X23 @ X26 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95               (k1_tsep_1 @ X25 @ X27 @ X24) @ X23)
% 0.76/0.95          | ~ (m1_subset_1 @ 
% 0.76/0.95               (k2_tmap_1 @ X25 @ X23 @ X26 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95                 (u1_struct_0 @ X23))))
% 0.76/0.95          | (v5_pre_topc @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X24) @ X24 @ X23)
% 0.76/0.95          | ~ (m1_subset_1 @ X26 @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))))
% 0.76/0.95          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))
% 0.76/0.95          | ~ (v1_funct_1 @ X26)
% 0.76/0.95          | ~ (r4_tsep_1 @ X25 @ X27 @ X24)
% 0.76/0.95          | ~ (m1_pre_topc @ X27 @ X25)
% 0.76/0.95          | (v2_struct_0 @ X27)
% 0.76/0.95          | ~ (l1_pre_topc @ X25)
% 0.76/0.95          | ~ (v2_pre_topc @ X25)
% 0.76/0.95          | (v2_struct_0 @ X25))),
% 0.76/0.95      inference('cnf', [status(esa)], [t129_tmap_1])).
% 0.76/0.95  thf('116', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ 
% 0.76/0.95               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.76/0.95               (u1_struct_0 @ X0))))
% 0.76/0.95          | (v2_struct_0 @ sk_A)
% 0.76/0.95          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.95          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ sk_D)
% 0.76/0.95          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.76/0.95          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.76/0.95          | ~ (v1_funct_1 @ X1)
% 0.76/0.95          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.76/0.95          | ~ (m1_subset_1 @ X1 @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.76/0.95          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E) @ sk_E @ X0)
% 0.76/0.95          | ~ (v5_pre_topc @ 
% 0.76/0.95               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.76/0.95               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.76/0.95          | ~ (v1_funct_2 @ 
% 0.76/0.95               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.76/0.95               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.76/0.95               (u1_struct_0 @ X0))
% 0.76/0.95          | ~ (v1_funct_1 @ 
% 0.76/0.95               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.76/0.95          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ sk_E)
% 0.76/0.95          | ~ (l1_pre_topc @ X0)
% 0.76/0.95          | ~ (v2_pre_topc @ X0)
% 0.76/0.95          | (v2_struct_0 @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['114', '115'])).
% 0.76/0.95  thf('117', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('120', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('121', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('122', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('123', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('124', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('125', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('126', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('127', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('128', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.76/0.95          | (v2_struct_0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ sk_D)
% 0.76/0.95          | ~ (v1_funct_1 @ X1)
% 0.76/0.95          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.76/0.95          | ~ (m1_subset_1 @ X1 @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.76/0.95          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E) @ sk_E @ X0)
% 0.76/0.95          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ sk_A @ X0)
% 0.76/0.95          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 0.76/0.95               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A))
% 0.76/0.95          | (v2_struct_0 @ sk_E)
% 0.76/0.95          | ~ (l1_pre_topc @ X0)
% 0.76/0.95          | ~ (v2_pre_topc @ X0)
% 0.76/0.95          | (v2_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['116', '117', '118', '119', '120', '121', '122', '123', 
% 0.76/0.95                 '124', '125', '126', '127'])).
% 0.76/0.95  thf('129', plain,
% 0.76/0.95      ((~ (l1_struct_0 @ sk_A)
% 0.76/0.95        | ~ (l1_struct_0 @ sk_A)
% 0.76/0.95        | (v2_struct_0 @ sk_B)
% 0.76/0.95        | ~ (v2_pre_topc @ sk_B)
% 0.76/0.95        | ~ (l1_pre_topc @ sk_B)
% 0.76/0.95        | (v2_struct_0 @ sk_E)
% 0.76/0.95        | ~ (v1_funct_1 @ 
% 0.76/0.95             (k2_tmap_1 @ sk_A @ sk_B @ 
% 0.76/0.95              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A))
% 0.76/0.95        | ~ (v1_funct_2 @ 
% 0.76/0.95             (k2_tmap_1 @ sk_A @ sk_B @ 
% 0.76/0.95              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A) @ 
% 0.76/0.95             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | ~ (v5_pre_topc @ 
% 0.76/0.95             (k2_tmap_1 @ sk_A @ sk_B @ 
% 0.76/0.95              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A) @ 
% 0.76/0.95             sk_A @ sk_B)
% 0.76/0.95        | (v5_pre_topc @ 
% 0.76/0.95           (k2_tmap_1 @ sk_A @ sk_B @ 
% 0.76/0.95            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_E) @ 
% 0.76/0.95           sk_E @ sk_B)
% 0.76/0.95        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 0.76/0.95             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.76/0.95        | (v2_struct_0 @ sk_D)
% 0.76/0.95        | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['113', '128'])).
% 0.76/0.95  thf('130', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.95      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.95  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.95      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.95  thf('132', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('133', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(t2_tsep_1, axiom,
% 0.76/0.95    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.76/0.95  thf('134', plain,
% 0.76/0.95      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.76/0.95      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.95  thf('135', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v2_struct_0 @ sk_A)
% 0.76/0.95          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.76/0.95              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 0.76/0.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 0.76/0.95  thf('136', plain,
% 0.76/0.95      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.95        | (v2_struct_0 @ sk_B)
% 0.76/0.95        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.76/0.95            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.76/0.95        | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['134', '135'])).
% 0.76/0.95  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('138', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(cc2_relset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.95  thf('139', plain,
% 0.76/0.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.76/0.95         ((v4_relat_1 @ X5 @ X6)
% 0.76/0.95          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.95  thf('140', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['138', '139'])).
% 0.76/0.95  thf(t209_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.76/0.95       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.76/0.95  thf('141', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((X0) = (k7_relat_1 @ X0 @ X1))
% 0.76/0.95          | ~ (v4_relat_1 @ X0 @ X1)
% 0.76/0.95          | ~ (v1_relat_1 @ X0))),
% 0.76/0.95      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.76/0.95  thf('142', plain,
% 0.76/0.95      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.95        | ((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['140', '141'])).
% 0.76/0.95  thf('143', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(cc1_relset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( v1_relat_1 @ C ) ))).
% 0.76/0.95  thf('144', plain,
% 0.76/0.95      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.95         ((v1_relat_1 @ X2)
% 0.76/0.95          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.95  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.95      inference('sup-', [status(thm)], ['143', '144'])).
% 0.76/0.95  thf('146', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.76/0.95      inference('demod', [status(thm)], ['142', '145'])).
% 0.76/0.95  thf('147', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_B)
% 0.76/0.95        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 0.76/0.95        | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['136', '137', '146'])).
% 0.76/0.95  thf('148', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('149', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_A)
% 0.76/0.95        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C)))),
% 0.76/0.95      inference('clc', [status(thm)], ['147', '148'])).
% 0.76/0.95  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('151', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('152', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('154', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('155', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('156', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('157', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('158', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('159', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('160', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('161', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('162', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('163', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('164', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('165', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('167', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_B)
% 0.76/0.95        | (v2_struct_0 @ sk_E)
% 0.76/0.95        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.76/0.95        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 0.76/0.95           sk_B)
% 0.76/0.95        | (v2_struct_0 @ sk_D)
% 0.76/0.95        | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['129', '130', '131', '132', '133', '151', '152', '153', 
% 0.76/0.95                 '154', '155', '156', '157', '158', '159', '160', '161', 
% 0.76/0.95                 '162', '163', '164', '165', '166'])).
% 0.76/0.95  thf('168', plain,
% 0.76/0.95      ((((v2_struct_0 @ sk_A)
% 0.76/0.95         | (v2_struct_0 @ sk_D)
% 0.76/0.95         | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 0.76/0.95            sk_B)
% 0.76/0.95         | (v2_struct_0 @ sk_E)
% 0.76/0.95         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['101', '167'])).
% 0.76/0.95  thf('169', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('170', plain,
% 0.76/0.95      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['71'])).
% 0.76/0.95  thf('171', plain,
% 0.76/0.95      ((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 0.76/0.95           sk_B))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['169', '170'])).
% 0.76/0.95  thf('172', plain,
% 0.76/0.95      ((((v2_struct_0 @ sk_B)
% 0.76/0.95         | (v2_struct_0 @ sk_E)
% 0.76/0.95         | (v2_struct_0 @ sk_D)
% 0.76/0.95         | (v2_struct_0 @ sk_A)))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)) & 
% 0.76/0.95             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['168', '171'])).
% 0.76/0.95  thf('173', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('174', plain,
% 0.76/0.95      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)) & 
% 0.76/0.95             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['172', '173'])).
% 0.76/0.95  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('176', plain,
% 0.76/0.95      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)) & 
% 0.76/0.95             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('clc', [status(thm)], ['174', '175'])).
% 0.76/0.95  thf('177', plain, (~ (v2_struct_0 @ sk_E)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('178', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_D))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)) & 
% 0.76/0.95             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('clc', [status(thm)], ['176', '177'])).
% 0.76/0.95  thf('179', plain, (~ (v2_struct_0 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('180', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.76/0.95       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['178', '179'])).
% 0.76/0.95  thf('181', plain,
% 0.76/0.95      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.76/0.95         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['100'])).
% 0.76/0.95  thf('182', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('183', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95           (k1_zfmisc_1 @ 
% 0.76/0.95            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '37', '40', '41', '42'])).
% 0.76/0.95  thf('184', plain,
% 0.76/0.95      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.95         ((v2_struct_0 @ X23)
% 0.76/0.95          | ~ (v2_pre_topc @ X23)
% 0.76/0.95          | ~ (l1_pre_topc @ X23)
% 0.76/0.95          | (v2_struct_0 @ X24)
% 0.76/0.95          | ~ (m1_pre_topc @ X24 @ X25)
% 0.76/0.95          | ~ (v1_funct_1 @ 
% 0.76/0.95               (k2_tmap_1 @ X25 @ X23 @ X26 @ (k1_tsep_1 @ X25 @ X27 @ X24)))
% 0.76/0.95          | ~ (v1_funct_2 @ 
% 0.76/0.95               (k2_tmap_1 @ X25 @ X23 @ X26 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95               (u1_struct_0 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95               (u1_struct_0 @ X23))
% 0.76/0.95          | ~ (v5_pre_topc @ 
% 0.76/0.95               (k2_tmap_1 @ X25 @ X23 @ X26 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95               (k1_tsep_1 @ X25 @ X27 @ X24) @ X23)
% 0.76/0.95          | ~ (m1_subset_1 @ 
% 0.76/0.95               (k2_tmap_1 @ X25 @ X23 @ X26 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X25 @ X27 @ X24)) @ 
% 0.76/0.95                 (u1_struct_0 @ X23))))
% 0.76/0.95          | (v5_pre_topc @ (k2_tmap_1 @ X25 @ X23 @ X26 @ X27) @ X27 @ X23)
% 0.76/0.95          | ~ (m1_subset_1 @ X26 @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))))
% 0.76/0.95          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))
% 0.76/0.95          | ~ (v1_funct_1 @ X26)
% 0.76/0.95          | ~ (r4_tsep_1 @ X25 @ X27 @ X24)
% 0.76/0.95          | ~ (m1_pre_topc @ X27 @ X25)
% 0.76/0.95          | (v2_struct_0 @ X27)
% 0.76/0.95          | ~ (l1_pre_topc @ X25)
% 0.76/0.95          | ~ (v2_pre_topc @ X25)
% 0.76/0.95          | (v2_struct_0 @ X25))),
% 0.76/0.95      inference('cnf', [status(esa)], [t129_tmap_1])).
% 0.76/0.95  thf('185', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.76/0.95          | (v2_struct_0 @ sk_A)
% 0.76/0.95          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.95          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ X1)
% 0.76/0.95          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.76/0.95          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.76/0.95          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.95          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (m1_subset_1 @ sk_C @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X1 @ sk_B)
% 0.76/0.95          | ~ (v5_pre_topc @ 
% 0.76/0.95               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 0.76/0.95               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 0.76/0.95          | ~ (v1_funct_2 @ 
% 0.76/0.95               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 0.76/0.95               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 0.76/0.95               (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (v1_funct_1 @ 
% 0.76/0.95               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 0.76/0.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ X0)
% 0.76/0.95          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.95          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.95          | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['183', '184'])).
% 0.76/0.95  thf('186', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('189', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('190', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('191', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('192', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('193', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.76/0.95          | (v2_struct_0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ X1)
% 0.76/0.95          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.76/0.95          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.76/0.95          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X1 @ sk_B)
% 0.76/0.95          | ~ (v5_pre_topc @ 
% 0.76/0.95               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 0.76/0.95               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 0.76/0.95          | ~ (v1_funct_2 @ 
% 0.76/0.95               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 0.76/0.95               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 0.76/0.95               (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (v1_funct_1 @ 
% 0.76/0.95               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 0.76/0.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ X0)
% 0.76/0.95          | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['185', '186', '187', '188', '189', '190', '191', '192'])).
% 0.76/0.95  thf('194', plain,
% 0.76/0.95      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 0.76/0.95           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.76/0.95           (u1_struct_0 @ sk_B))
% 0.76/0.95        | (v2_struct_0 @ sk_B)
% 0.76/0.95        | (v2_struct_0 @ sk_E)
% 0.76/0.95        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.76/0.95        | ~ (v1_funct_1 @ 
% 0.76/0.95             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.76/0.95        | ~ (v5_pre_topc @ 
% 0.76/0.95             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.76/0.95             (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 0.76/0.95        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.76/0.95        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.76/0.95        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.76/0.95        | (v2_struct_0 @ sk_D)
% 0.76/0.95        | (v2_struct_0 @ sk_A)
% 0.76/0.95        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['182', '193'])).
% 0.76/0.95  thf('195', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('196', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('197', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('198', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('199', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('200', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('202', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('203', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('204', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('205', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('206', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('207', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('208', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('209', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.95      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.95  thf('210', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_B)
% 0.76/0.95        | (v2_struct_0 @ sk_E)
% 0.76/0.95        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.76/0.95        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 0.76/0.95           sk_B)
% 0.76/0.95        | (v2_struct_0 @ sk_D)
% 0.76/0.95        | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['194', '195', '196', '197', '198', '199', '200', '201', 
% 0.76/0.95                 '202', '203', '204', '205', '206', '207', '208', '209'])).
% 0.76/0.95  thf('211', plain,
% 0.76/0.95      ((((v2_struct_0 @ sk_A)
% 0.76/0.95         | (v2_struct_0 @ sk_D)
% 0.76/0.95         | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 0.76/0.95            sk_B)
% 0.76/0.95         | (v2_struct_0 @ sk_E)
% 0.76/0.95         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['181', '210'])).
% 0.76/0.95  thf('212', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('213', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.76/0.95        | (v1_funct_1 @ sk_C))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('214', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.76/0.95         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['213'])).
% 0.76/0.95  thf('215', plain,
% 0.76/0.95      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 0.76/0.95         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['212', '214'])).
% 0.76/0.95  thf('216', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95           (k1_zfmisc_1 @ 
% 0.76/0.95            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95             sk_B)
% 0.76/0.95        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.76/0.95        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.76/0.95             sk_B)
% 0.76/0.95        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.76/0.95             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.76/0.95        | ~ (m1_subset_1 @ sk_C @ 
% 0.76/0.95             (k1_zfmisc_1 @ 
% 0.76/0.95              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.76/0.95        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | ~ (v1_funct_1 @ sk_C))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('217', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('218', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('219', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95           (k1_zfmisc_1 @ 
% 0.76/0.95            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['34', '37', '40', '41', '42'])).
% 0.76/0.95  thf('220', plain,
% 0.76/0.95      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 0.76/0.95         (k1_zfmisc_1 @ 
% 0.76/0.95          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | ~ (l1_struct_0 @ sk_E))),
% 0.76/0.95      inference('sup+', [status(thm)], ['218', '219'])).
% 0.76/0.95  thf('221', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('222', plain,
% 0.76/0.95      (![X13 : $i, X14 : $i]:
% 0.76/0.95         (~ (m1_pre_topc @ X13 @ X14)
% 0.76/0.95          | (l1_pre_topc @ X13)
% 0.76/0.95          | ~ (l1_pre_topc @ X14))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.76/0.95  thf('223', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_E))),
% 0.76/0.95      inference('sup-', [status(thm)], ['221', '222'])).
% 0.76/0.95  thf('224', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('225', plain, ((l1_pre_topc @ sk_E)),
% 0.76/0.95      inference('demod', [status(thm)], ['223', '224'])).
% 0.76/0.95  thf('226', plain,
% 0.76/0.95      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.95  thf('227', plain, ((l1_struct_0 @ sk_E)),
% 0.76/0.95      inference('sup-', [status(thm)], ['225', '226'])).
% 0.76/0.95  thf('228', plain,
% 0.76/0.95      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('demod', [status(thm)], ['220', '227'])).
% 0.76/0.95  thf('229', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('230', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('231', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | (v1_funct_1 @ sk_C))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('232', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.76/0.95         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('split', [status(esa)], ['231'])).
% 0.76/0.95  thf('233', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.76/0.95  thf('234', plain,
% 0.76/0.95      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('split', [status(esa)], ['71'])).
% 0.76/0.95  thf('235', plain,
% 0.76/0.95      ((~ (l1_struct_0 @ sk_E))
% 0.76/0.95         <= (~
% 0.76/0.95             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['233', '234'])).
% 0.76/0.95  thf('236', plain, ((l1_struct_0 @ sk_E)),
% 0.76/0.95      inference('sup-', [status(thm)], ['225', '226'])).
% 0.76/0.95  thf('237', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['235', '236'])).
% 0.76/0.95  thf('238', plain,
% 0.76/0.95      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)], ['237'])).
% 0.76/0.95  thf('239', plain,
% 0.76/0.95      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['232', '238'])).
% 0.76/0.95  thf('240', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('241', plain,
% 0.76/0.95      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 0.76/0.95        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['239', '240'])).
% 0.76/0.95  thf('242', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('243', plain,
% 0.76/0.95      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.76/0.95        | (v1_funct_1 @ sk_C))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('244', plain,
% 0.76/0.95      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.76/0.95         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.95      inference('split', [status(esa)], ['243'])).
% 0.76/0.95  thf('245', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (l1_struct_0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.76/0.95  thf('246', plain,
% 0.76/0.95      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.76/0.95         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.95      inference('split', [status(esa)], ['71'])).
% 0.76/0.95  thf('247', plain,
% 0.76/0.95      ((~ (l1_struct_0 @ sk_E))
% 0.76/0.95         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['245', '246'])).
% 0.76/0.95  thf('248', plain, ((l1_struct_0 @ sk_E)),
% 0.76/0.95      inference('sup-', [status(thm)], ['225', '226'])).
% 0.76/0.95  thf('249', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.76/0.95      inference('demod', [status(thm)], ['247', '248'])).
% 0.76/0.95  thf('250', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)], ['249'])).
% 0.76/0.95  thf('251', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['244', '250'])).
% 0.76/0.95  thf('252', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('253', plain,
% 0.76/0.95      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('demod', [status(thm)], ['251', '252'])).
% 0.76/0.95  thf('254', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('255', plain,
% 0.76/0.95      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('demod', [status(thm)], ['44', '51'])).
% 0.76/0.95  thf('256', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('257', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('258', plain,
% 0.76/0.95      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 0.76/0.95        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['77', '78'])).
% 0.76/0.95  thf('259', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('260', plain,
% 0.76/0.95      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.76/0.95      inference('demod', [status(thm)], ['90', '91'])).
% 0.76/0.95  thf('261', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('262', plain,
% 0.76/0.95      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('263', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('264', plain,
% 0.76/0.95      ((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 0.76/0.95           sk_B)
% 0.76/0.95        | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 0.76/0.95             sk_B)
% 0.76/0.95        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['216', '217', '228', '229', '230', '241', '242', '253', 
% 0.76/0.95                 '254', '255', '256', '257', '258', '259', '260', '261', 
% 0.76/0.95                 '262', '263'])).
% 0.76/0.95  thf('265', plain,
% 0.76/0.95      (((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.76/0.95         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 0.76/0.95              sk_D @ sk_B)))
% 0.76/0.95         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['215', '264'])).
% 0.76/0.95  thf('266', plain,
% 0.76/0.95      ((((v2_struct_0 @ sk_B)
% 0.76/0.95         | (v2_struct_0 @ sk_E)
% 0.76/0.95         | (v2_struct_0 @ sk_D)
% 0.76/0.95         | (v2_struct_0 @ sk_A)
% 0.76/0.95         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.76/0.95         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['211', '265'])).
% 0.76/0.95  thf('267', plain,
% 0.76/0.95      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.76/0.95         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['100'])).
% 0.76/0.95  thf('268', plain,
% 0.76/0.95      ((((v2_struct_0 @ sk_B)
% 0.76/0.95         | (v2_struct_0 @ sk_E)
% 0.76/0.95         | (v2_struct_0 @ sk_D)
% 0.76/0.95         | (v2_struct_0 @ sk_A)))
% 0.76/0.95         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['266', '267'])).
% 0.76/0.95  thf('269', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('270', plain,
% 0.76/0.95      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.76/0.95         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['268', '269'])).
% 0.76/0.95  thf('271', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('272', plain,
% 0.76/0.95      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.76/0.95         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('clc', [status(thm)], ['270', '271'])).
% 0.76/0.95  thf('273', plain, (~ (v2_struct_0 @ sk_E)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('274', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_D))
% 0.76/0.95         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.76/0.95             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('clc', [status(thm)], ['272', '273'])).
% 0.76/0.95  thf('275', plain, (~ (v2_struct_0 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('276', plain,
% 0.76/0.95      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.76/0.95       ~
% 0.76/0.95       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['274', '275'])).
% 0.76/0.95  thf('277', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.76/0.95        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('278', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.76/0.95       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.76/0.95      inference('split', [status(esa)], ['277'])).
% 0.76/0.95  thf('279', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)], ['180', '276', '278'])).
% 0.76/0.95  thf('280', plain,
% 0.76/0.95      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['99', '279'])).
% 0.76/0.95  thf('281', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v2_struct_0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ sk_D)
% 0.76/0.95          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.76/0.95          | (v5_pre_topc @ 
% 0.76/0.95             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.76/0.95             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 0.76/0.95          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95               (k1_zfmisc_1 @ 
% 0.76/0.95                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.76/0.95          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.76/0.95               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.95          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.76/0.95          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.95          | (v2_struct_0 @ X0)
% 0.76/0.95          | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['95', '280'])).
% 0.76/0.95  thf('282', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 0.76/0.95           (k1_zfmisc_1 @ 
% 0.76/0.95            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.76/0.95        | (v2_struct_0 @ sk_B)
% 0.76/0.95        | (v2_struct_0 @ sk_E)
% 0.76/0.95        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.76/0.95        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.76/0.95        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.76/0.95             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.76/0.95        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95             sk_B)
% 0.76/0.95        | (v5_pre_topc @ 
% 0.76/0.95           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.76/0.95           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 0.76/0.95        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.76/0.95        | (v2_struct_0 @ sk_D)
% 0.76/0.95        | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['21', '281'])).
% 0.76/0.95  thf('283', plain,
% 0.76/0.95      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 0.76/0.95        (k1_zfmisc_1 @ 
% 0.76/0.95         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.95      inference('demod', [status(thm)], ['220', '227'])).
% 0.76/0.95  thf('284', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('285', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('286', plain,
% 0.76/0.95      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('demod', [status(thm)], ['251', '252'])).
% 0.76/0.95  thf('287', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('288', plain,
% 0.76/0.95      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 0.76/0.95        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['239', '240'])).
% 0.76/0.95  thf('289', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('290', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.76/0.95         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['213'])).
% 0.76/0.95  thf('291', plain,
% 0.76/0.95      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.76/0.95         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.76/0.95      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('292', plain,
% 0.76/0.95      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 0.76/0.95         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.76/0.95               sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['290', '291'])).
% 0.76/0.95  thf('293', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.76/0.95        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('294', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.76/0.95       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.76/0.95      inference('split', [status(esa)], ['293'])).
% 0.76/0.95  thf('295', plain,
% 0.76/0.95      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)], ['180', '276', '294'])).
% 0.76/0.95  thf('296', plain,
% 0.76/0.95      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['292', '295'])).
% 0.76/0.95  thf('297', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('298', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.76/0.95      inference('clc', [status(thm)], ['149', '150'])).
% 0.76/0.95  thf('299', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('300', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('301', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_B)
% 0.76/0.95        | (v2_struct_0 @ sk_E)
% 0.76/0.95        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.76/0.95        | (v2_struct_0 @ sk_D)
% 0.76/0.95        | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['282', '283', '284', '285', '286', '287', '288', '289', 
% 0.76/0.95                 '296', '297', '298', '299', '300'])).
% 0.76/0.95  thf('302', plain,
% 0.76/0.95      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.76/0.95         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['71'])).
% 0.76/0.95  thf('303', plain, (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)], ['180', '276'])).
% 0.76/0.95  thf('304', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['302', '303'])).
% 0.76/0.95  thf('305', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_A)
% 0.76/0.95        | (v2_struct_0 @ sk_D)
% 0.76/0.95        | (v2_struct_0 @ sk_E)
% 0.76/0.95        | (v2_struct_0 @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['301', '304'])).
% 0.76/0.95  thf('306', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('307', plain,
% 0.76/0.95      (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['305', '306'])).
% 0.76/0.95  thf('308', plain, (~ (v2_struct_0 @ sk_E)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('309', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.76/0.95      inference('clc', [status(thm)], ['307', '308'])).
% 0.76/0.95  thf('310', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('311', plain, ((v2_struct_0 @ sk_D)),
% 0.76/0.95      inference('clc', [status(thm)], ['309', '310'])).
% 0.76/0.95  thf('312', plain, ($false), inference('demod', [status(thm)], ['0', '311'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
