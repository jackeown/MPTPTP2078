%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bedhRY2EHf

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:47 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 177 expanded)
%              Number of leaves         :   44 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          : 1061 (4427 expanded)
%              Number of equality atoms :   34 (  92 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t61_tmap_1,conjecture,(
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
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) )
                       => ( ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E )
                          = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) )
                         => ( ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E )
                            = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_E )
        = ( k9_relat_1 @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('4',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X33 )
      | ( r1_tarski @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
        & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( zip_tseitin_0 @ X23 @ X20 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_0 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ X14 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('23',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 )
        = ( k7_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( ( k7_relset_1 @ X7 @ X8 @ X6 @ X9 )
        = ( k9_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 )
        = ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( ( k7_relset_1 @ X7 @ X8 @ X6 @ X9 )
        = ( k9_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( ( k2_tmap_1 @ X28 @ X26 @ X29 @ X27 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) @ X29 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44','45','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['36','53'])).

thf('55',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','54'])).

thf('56',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('68',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['65','66','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bedhRY2EHf
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:54:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.18/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.49  % Solved by: fo/fo7.sh
% 0.18/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.49  % done 73 iterations in 0.045s
% 0.18/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.49  % SZS output start Refutation
% 0.18/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.18/0.49  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.18/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.18/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.18/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.18/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.18/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.18/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.18/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.18/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.49  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.18/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.18/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.18/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.18/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.18/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.49  thf(t61_tmap_1, conjecture,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.18/0.49             ( l1_pre_topc @ B ) ) =>
% 0.18/0.49           ( ![C:$i]:
% 0.18/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.18/0.49               ( ![D:$i]:
% 0.18/0.49                 ( ( ( v1_funct_1 @ D ) & 
% 0.18/0.49                     ( v1_funct_2 @
% 0.18/0.49                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.18/0.49                     ( m1_subset_1 @
% 0.18/0.49                       D @ 
% 0.18/0.49                       ( k1_zfmisc_1 @
% 0.18/0.49                         ( k2_zfmisc_1 @
% 0.18/0.49                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.18/0.49                   ( ![E:$i]:
% 0.18/0.49                     ( ( m1_subset_1 @
% 0.18/0.49                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.18/0.49                       ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.18/0.49                         ( ( k7_relset_1 @
% 0.18/0.49                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) =
% 0.18/0.49                           ( k7_relset_1 @
% 0.18/0.49                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.18/0.49                             ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.49    (~( ![A:$i]:
% 0.18/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.18/0.49            ( l1_pre_topc @ A ) ) =>
% 0.18/0.49          ( ![B:$i]:
% 0.18/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.18/0.49                ( l1_pre_topc @ B ) ) =>
% 0.18/0.49              ( ![C:$i]:
% 0.18/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.18/0.49                  ( ![D:$i]:
% 0.18/0.49                    ( ( ( v1_funct_1 @ D ) & 
% 0.18/0.49                        ( v1_funct_2 @
% 0.18/0.49                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.18/0.49                        ( m1_subset_1 @
% 0.18/0.49                          D @ 
% 0.18/0.49                          ( k1_zfmisc_1 @
% 0.18/0.49                            ( k2_zfmisc_1 @
% 0.18/0.49                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.18/0.49                      ( ![E:$i]:
% 0.18/0.49                        ( ( m1_subset_1 @
% 0.18/0.49                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.18/0.49                          ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.18/0.49                            ( ( k7_relset_1 @
% 0.18/0.49                                ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.18/0.49                                D @ E ) =
% 0.18/0.49                              ( k7_relset_1 @
% 0.18/0.49                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.18/0.49                                ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.18/0.49    inference('cnf.neg', [status(esa)], [t61_tmap_1])).
% 0.18/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('1', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(t162_relat_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ A ) =>
% 0.18/0.49       ( ![B:$i,C:$i]:
% 0.18/0.49         ( ( r1_tarski @ B @ C ) =>
% 0.18/0.49           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.18/0.49             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.18/0.49  thf('2', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.18/0.49          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.18/0.49              = (k9_relat_1 @ X2 @ X0))
% 0.18/0.49          | ~ (v1_relat_1 @ X2))),
% 0.18/0.49      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.18/0.49  thf('3', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (v1_relat_1 @ X0)
% 0.18/0.49          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_E)
% 0.18/0.49              = (k9_relat_1 @ X0 @ sk_E)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.49  thf(t2_tsep_1, axiom,
% 0.18/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.18/0.49  thf('4', plain,
% 0.18/0.49      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 0.18/0.49      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.18/0.49  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(t4_tsep_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.18/0.49           ( ![C:$i]:
% 0.18/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.18/0.49               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.18/0.49                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.18/0.49  thf('6', plain,
% 0.18/0.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.18/0.49         (~ (m1_pre_topc @ X31 @ X32)
% 0.18/0.49          | ~ (m1_pre_topc @ X31 @ X33)
% 0.18/0.49          | (r1_tarski @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X33))
% 0.18/0.49          | ~ (m1_pre_topc @ X33 @ X32)
% 0.18/0.49          | ~ (l1_pre_topc @ X32)
% 0.18/0.49          | ~ (v2_pre_topc @ X32))),
% 0.18/0.49      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.18/0.49  thf('7', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (v2_pre_topc @ sk_B)
% 0.18/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.18/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.18/0.49          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.18/0.49          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.18/0.49  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('10', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.18/0.49          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.18/0.49          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.18/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.18/0.49  thf('11', plain,
% 0.18/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.18/0.49        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.18/0.49        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['4', '10'])).
% 0.18/0.49  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('13', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('14', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.18/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.18/0.49  thf('15', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ 
% 0.18/0.49        (k1_zfmisc_1 @ 
% 0.18/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(t38_funct_2, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.49     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.18/0.49         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.18/0.49       ( ( r1_tarski @ C @ A ) =>
% 0.18/0.49         ( ( ( m1_subset_1 @
% 0.18/0.49               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.18/0.49               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.18/0.49             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.18/0.49             ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) ) | 
% 0.18/0.49           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.18/0.49  thf(zf_stmt_2, axiom,
% 0.18/0.49    (![B:$i,A:$i]:
% 0.18/0.49     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.18/0.49       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.18/0.49  thf(zf_stmt_4, axiom,
% 0.18/0.49    (![D:$i,C:$i,B:$i,A:$i]:
% 0.18/0.49     ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.18/0.49       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 0.18/0.49         ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.18/0.49         ( m1_subset_1 @
% 0.18/0.49           ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.18/0.49           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_5, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.18/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.18/0.49       ( ( r1_tarski @ C @ A ) =>
% 0.18/0.49         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ))).
% 0.18/0.49  thf('16', plain,
% 0.18/0.49      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.18/0.49         (~ (r1_tarski @ X20 @ X21)
% 0.18/0.49          | (zip_tseitin_1 @ X22 @ X21)
% 0.18/0.49          | ~ (v1_funct_1 @ X23)
% 0.18/0.49          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.18/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.18/0.49          | (zip_tseitin_0 @ X23 @ X20 @ X22 @ X21))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.18/0.49  thf('17', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((zip_tseitin_0 @ sk_D @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.49           (u1_struct_0 @ sk_B))
% 0.18/0.49          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.18/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.18/0.49          | (zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.18/0.49          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.18/0.49  thf('18', plain,
% 0.18/0.49      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('20', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((zip_tseitin_0 @ sk_D @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.49           (u1_struct_0 @ sk_B))
% 0.18/0.49          | (zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.18/0.49          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.18/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.18/0.49  thf('21', plain,
% 0.18/0.49      (((zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.18/0.49        | (zip_tseitin_0 @ sk_D @ (u1_struct_0 @ sk_C) @ 
% 0.18/0.49           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['14', '20'])).
% 0.18/0.49  thf('22', plain,
% 0.18/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.18/0.49         ((m1_subset_1 @ (k2_partfun1 @ X14 @ X15 @ X16 @ X17) @ 
% 0.18/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.18/0.49          | ~ (zip_tseitin_0 @ X16 @ X17 @ X15 @ X14))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.18/0.49  thf('23', plain,
% 0.18/0.49      (((zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.18/0.49        | (m1_subset_1 @ 
% 0.18/0.49           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.18/0.49            (u1_struct_0 @ sk_C)) @ 
% 0.18/0.49           (k1_zfmisc_1 @ 
% 0.18/0.49            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.18/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.18/0.49  thf('24', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ 
% 0.18/0.49        (k1_zfmisc_1 @ 
% 0.18/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(redefinition_k2_partfun1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.18/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.18/0.49       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.18/0.49  thf('25', plain,
% 0.18/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.18/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.18/0.49          | ~ (v1_funct_1 @ X10)
% 0.18/0.49          | ((k2_partfun1 @ X11 @ X12 @ X10 @ X13) = (k7_relat_1 @ X10 @ X13)))),
% 0.18/0.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.18/0.49  thf('26', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.18/0.49            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.18/0.49          | ~ (v1_funct_1 @ sk_D))),
% 0.18/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.18/0.49  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('28', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.18/0.49           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.18/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.18/0.49  thf('29', plain,
% 0.18/0.49      (((zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.18/0.49        | (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.18/0.49           (k1_zfmisc_1 @ 
% 0.18/0.49            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.18/0.49      inference('demod', [status(thm)], ['23', '28'])).
% 0.18/0.49  thf(redefinition_k7_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.18/0.49  thf('30', plain,
% 0.18/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.18/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.18/0.49          | ((k7_relset_1 @ X7 @ X8 @ X6 @ X9) = (k9_relat_1 @ X6 @ X9)))),
% 0.18/0.49      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.18/0.49  thf('31', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.18/0.49          | ((k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.49              (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0)
% 0.18/0.49              = (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.18/0.49  thf('32', plain,
% 0.18/0.49      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.18/0.49         sk_E)
% 0.18/0.49         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.49             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('33', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ 
% 0.18/0.49        (k1_zfmisc_1 @ 
% 0.18/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('34', plain,
% 0.18/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.18/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.18/0.49          | ((k7_relset_1 @ X7 @ X8 @ X6 @ X9) = (k9_relat_1 @ X6 @ X9)))),
% 0.18/0.49      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.18/0.49  thf('35', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.18/0.49           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.18/0.49  thf('36', plain,
% 0.18/0.49      (((k9_relat_1 @ sk_D @ sk_E)
% 0.18/0.49         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.49             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.18/0.49      inference('demod', [status(thm)], ['32', '35'])).
% 0.18/0.49  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('38', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ 
% 0.18/0.49        (k1_zfmisc_1 @ 
% 0.18/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(d4_tmap_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.18/0.49             ( l1_pre_topc @ B ) ) =>
% 0.18/0.49           ( ![C:$i]:
% 0.18/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.18/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.18/0.49                 ( m1_subset_1 @
% 0.18/0.49                   C @ 
% 0.18/0.49                   ( k1_zfmisc_1 @
% 0.18/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.18/0.49               ( ![D:$i]:
% 0.18/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.18/0.49                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.18/0.49                     ( k2_partfun1 @
% 0.18/0.49                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.18/0.49                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.49  thf('39', plain,
% 0.18/0.49      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.18/0.49         ((v2_struct_0 @ X26)
% 0.18/0.49          | ~ (v2_pre_topc @ X26)
% 0.18/0.49          | ~ (l1_pre_topc @ X26)
% 0.18/0.49          | ~ (m1_pre_topc @ X27 @ X28)
% 0.18/0.49          | ((k2_tmap_1 @ X28 @ X26 @ X29 @ X27)
% 0.18/0.49              = (k2_partfun1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26) @ 
% 0.18/0.49                 X29 @ (u1_struct_0 @ X27)))
% 0.18/0.49          | ~ (m1_subset_1 @ X29 @ 
% 0.18/0.49               (k1_zfmisc_1 @ 
% 0.18/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 0.18/0.49          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 0.18/0.49          | ~ (v1_funct_1 @ X29)
% 0.18/0.49          | ~ (l1_pre_topc @ X28)
% 0.18/0.49          | ~ (v2_pre_topc @ X28)
% 0.18/0.49          | (v2_struct_0 @ X28))),
% 0.18/0.49      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.18/0.49  thf('40', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((v2_struct_0 @ sk_B)
% 0.18/0.49          | ~ (v2_pre_topc @ sk_B)
% 0.18/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.18/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.18/0.49          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.18/0.49          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.18/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.49                 sk_D @ (u1_struct_0 @ X0)))
% 0.18/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.18/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.18/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.18/0.49          | (v2_struct_0 @ sk_A))),
% 0.18/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.18/0.49  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('44', plain,
% 0.18/0.49      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('45', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.18/0.49           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.18/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.18/0.49  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('48', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((v2_struct_0 @ sk_B)
% 0.18/0.49          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.18/0.49              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.18/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.18/0.49          | (v2_struct_0 @ sk_A))),
% 0.18/0.49      inference('demod', [status(thm)],
% 0.18/0.49                ['40', '41', '42', '43', '44', '45', '46', '47'])).
% 0.18/0.49  thf('49', plain,
% 0.18/0.49      (((v2_struct_0 @ sk_A)
% 0.18/0.49        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.18/0.49            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.18/0.49        | (v2_struct_0 @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['37', '48'])).
% 0.18/0.49  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('51', plain,
% 0.18/0.49      (((v2_struct_0 @ sk_B)
% 0.18/0.49        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.18/0.49            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.18/0.49      inference('clc', [status(thm)], ['49', '50'])).
% 0.18/0.49  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('53', plain,
% 0.18/0.49      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.18/0.49         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.18/0.49      inference('clc', [status(thm)], ['51', '52'])).
% 0.18/0.49  thf('54', plain,
% 0.18/0.49      (((k9_relat_1 @ sk_D @ sk_E)
% 0.18/0.49         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.49             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.18/0.49      inference('demod', [status(thm)], ['36', '53'])).
% 0.18/0.49  thf('55', plain,
% 0.18/0.49      ((((k9_relat_1 @ sk_D @ sk_E)
% 0.18/0.49          != (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))
% 0.18/0.49        | (zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['31', '54'])).
% 0.18/0.49  thf('56', plain,
% 0.18/0.49      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 0.18/0.49        | ~ (v1_relat_1 @ sk_D)
% 0.18/0.49        | (zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['3', '55'])).
% 0.18/0.49  thf('57', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ 
% 0.18/0.49        (k1_zfmisc_1 @ 
% 0.18/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(cc1_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( v1_relat_1 @ C ) ))).
% 0.18/0.49  thf('58', plain,
% 0.18/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.49         ((v1_relat_1 @ X3)
% 0.18/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.18/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.18/0.49  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.18/0.49  thf('60', plain,
% 0.18/0.49      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 0.18/0.49        | (zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.18/0.49      inference('demod', [status(thm)], ['56', '59'])).
% 0.18/0.49  thf('61', plain,
% 0.18/0.49      ((zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.18/0.49      inference('simplify', [status(thm)], ['60'])).
% 0.18/0.49  thf('62', plain,
% 0.18/0.49      (![X18 : $i, X19 : $i]:
% 0.18/0.49         (((X18) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X18 @ X19))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.18/0.49  thf('63', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.18/0.49  thf(fc2_struct_0, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.18/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.18/0.49  thf('64', plain,
% 0.18/0.49      (![X25 : $i]:
% 0.18/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.18/0.49          | ~ (l1_struct_0 @ X25)
% 0.18/0.49          | (v2_struct_0 @ X25))),
% 0.18/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.18/0.49  thf('65', plain,
% 0.18/0.49      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.18/0.49        | (v2_struct_0 @ sk_A)
% 0.18/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.18/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.18/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.18/0.49  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.18/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.18/0.49  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(dt_l1_pre_topc, axiom,
% 0.18/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.18/0.49  thf('68', plain,
% 0.18/0.49      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.18/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.18/0.49  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.18/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.18/0.49  thf('70', plain, ((v2_struct_0 @ sk_A)),
% 0.18/0.49      inference('demod', [status(thm)], ['65', '66', '69'])).
% 0.18/0.49  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.18/0.49  
% 0.18/0.49  % SZS output end Refutation
% 0.18/0.49  
% 0.18/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
