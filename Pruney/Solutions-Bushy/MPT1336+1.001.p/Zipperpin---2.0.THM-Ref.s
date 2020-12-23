%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1336+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XZjL9usSFj

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:31 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 357 expanded)
%              Number of leaves         :   56 ( 133 expanded)
%              Depth                    :   18
%              Number of atoms          : 1229 (7351 expanded)
%              Number of equality atoms :   27 ( 139 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_funct_3_type,type,(
    k3_funct_3: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t59_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                 => ( ( ( v5_pre_topc @ C @ A @ B )
                      & ( v1_tops_2 @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ( ( E
                            = ( k9_relat_1 @ ( k3_funct_3 @ C ) @ D ) )
                         => ( v1_tops_2 @ E @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                   => ( ( ( v5_pre_topc @ C @ A @ B )
                        & ( v1_tops_2 @ D @ B ) )
                     => ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                         => ( ( E
                              = ( k9_relat_1 @ ( k3_funct_3 @ C ) @ D ) )
                           => ( v1_tops_2 @ E @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_tops_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( v5_pre_topc @ C @ A @ B )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( v3_pre_topc @ D @ B )
                       => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( ( k2_struct_0 @ B )
          = k1_xboole_0 )
       => ( ( k2_struct_0 @ A )
          = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_1 @ X31 @ X32 )
      | ( ( k2_struct_0 @ X31 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v5_pre_topc @ C @ A @ B )
      <=> ! [D: $i] :
            ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
       => ( ( v3_pre_topc @ D @ B )
         => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( zip_tseitin_1 @ B @ A )
               => ( zip_tseitin_3 @ C @ B @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 )
      | ( zip_tseitin_3 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_3 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( zip_tseitin_3 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_3 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v5_pre_topc @ X40 @ X38 @ X39 )
      | ( zip_tseitin_2 @ X41 @ X40 @ X39 @ X38 )
      | ~ ( zip_tseitin_3 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ sk_C_1 @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_2 @ X0 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_E_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v1_tops_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_E_2 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_tops_2 @ sk_E_2 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_E_2 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_tops_2 @ sk_E_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_E_2 ),
    inference(clc,[status(thm)],['19','20'])).

thf(dt_k3_funct_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k3_funct_3 @ A ) )
        & ( v1_funct_1 @ ( k3_funct_3 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k3_funct_3 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_3])).

thf('23',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k3_funct_3 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_3])).

thf('24',plain,
    ( sk_E_2
    = ( k9_relat_1 @ ( k3_funct_3 @ sk_C_1 ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_10,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k9_relat_1 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X13 @ X9 @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('26',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X13 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k3_funct_3 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k3_funct_3 @ sk_C_1 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k3_funct_3 @ sk_C_1 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X6 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('40',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( m1_subset_1 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) @ X36 @ X33 ) @ X35 )
      | ~ ( v3_pre_topc @ X33 @ X34 )
      | ~ ( zip_tseitin_2 @ X33 @ X36 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X1 @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ sk_B )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_tops_2 @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D_2 )
      | ~ ( v1_tops_2 @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_tops_2 @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_2 )
      | ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    v3_pre_topc @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X1 @ sk_B @ X0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['46','56'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('60',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('63',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('64',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k3_funct_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t24_funct_3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k3_funct_3 @ B ) ) )
       => ( ( k1_funct_1 @ ( k3_funct_3 @ B ) @ A )
          = ( k10_relat_1 @ B @ A ) ) ) ) )).

thf('65',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ ( k3_funct_3 @ X27 ) ) )
      | ( ( k1_funct_1 @ ( k3_funct_3 @ X27 ) @ X26 )
        = ( k10_relat_1 @ X27 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_3])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_funct_1 @ ( k3_funct_3 @ sk_C_1 ) @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) )
      = ( k10_relat_1 @ sk_C_1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k1_funct_1 @ X3 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('71',plain,
    ( ( sk_C @ sk_E_2 @ sk_A )
    = ( k1_funct_1 @ ( k3_funct_3 @ sk_C_1 ) @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C @ sk_E_2 @ sk_A )
    = ( k10_relat_1 @ sk_C_1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','71'])).

thf('73',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['58','61','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X16 @ X17 ) @ X17 )
      | ( v1_tops_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_E_2 @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_tops_2 @ sk_E_2 @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_tops_2 @ sk_E_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ~ ( v3_pre_topc @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','80'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('86',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['83','84','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).


%------------------------------------------------------------------------------
