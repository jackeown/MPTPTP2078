%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qZ95VWjE0G

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:07 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 428 expanded)
%              Number of leaves         :   40 ( 143 expanded)
%              Depth                    :   26
%              Number of atoms          : 1980 (14306 expanded)
%              Number of equality atoms :   19 (  43 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t78_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

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
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( zip_tseitin_0 @ X17 @ X14 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_E @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_E @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ X8 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('15',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X5 @ X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( r2_funct_2 @ X5 @ X6 @ X4 @ X7 )
      | ( X4 != X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_funct_2 @ X5 @ X6 @ X7 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X1 @ X2 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v1_funct_2 @ ( k2_partfun1 @ X8 @ X9 @ X10 @ X11 ) @ X11 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( ( k2_tmap_1 @ X22 @ X20 @ X23 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('32',plain,(
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
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('46',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','44','45'])).

thf('47',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('48',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('49',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('51',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('52',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t77_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ F @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                              & ( m1_pre_topc @ D @ C ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) @ ( k3_tmap_1 @ X28 @ X26 @ X30 @ X27 @ X29 ) @ ( k2_tmap_1 @ X28 @ X26 @ X31 @ X27 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X26 ) @ X29 @ ( k2_tmap_1 @ X28 @ X26 @ X31 @ X30 ) )
      | ~ ( m1_pre_topc @ X27 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('56',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('57',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('79',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('83',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('84',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qZ95VWjE0G
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 267 iterations in 0.344s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.80  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.58/0.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.58/0.80  thf(sk_E_type, type, sk_E: $i).
% 0.58/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.80  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.58/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.80  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.58/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.80  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.58/0.80  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.80  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.80  thf(t78_tmap_1, conjecture,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.80             ( l1_pre_topc @ B ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.80               ( ![D:$i]:
% 0.58/0.80                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.80                   ( ![E:$i]:
% 0.58/0.80                     ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.80                         ( v1_funct_2 @
% 0.58/0.80                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                         ( m1_subset_1 @
% 0.58/0.80                           E @ 
% 0.58/0.80                           ( k1_zfmisc_1 @
% 0.58/0.80                             ( k2_zfmisc_1 @
% 0.58/0.80                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.80                       ( ( m1_pre_topc @ C @ D ) =>
% 0.58/0.80                         ( r2_funct_2 @
% 0.58/0.80                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.80                           ( k3_tmap_1 @
% 0.58/0.80                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.58/0.80                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i]:
% 0.58/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.80            ( l1_pre_topc @ A ) ) =>
% 0.58/0.80          ( ![B:$i]:
% 0.58/0.80            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.80                ( l1_pre_topc @ B ) ) =>
% 0.58/0.80              ( ![C:$i]:
% 0.58/0.80                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.80                  ( ![D:$i]:
% 0.58/0.80                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.80                      ( ![E:$i]:
% 0.58/0.80                        ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.80                            ( v1_funct_2 @
% 0.58/0.80                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                            ( m1_subset_1 @
% 0.58/0.80                              E @ 
% 0.58/0.80                              ( k1_zfmisc_1 @
% 0.58/0.80                                ( k2_zfmisc_1 @
% 0.58/0.80                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.80                          ( ( m1_pre_topc @ C @ D ) =>
% 0.58/0.80                            ( r2_funct_2 @
% 0.58/0.80                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.80                              ( k3_tmap_1 @
% 0.58/0.80                                A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.58/0.80                              ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t78_tmap_1])).
% 0.58/0.80  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t35_borsuk_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_pre_topc @ A ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_pre_topc @ B @ A ) =>
% 0.58/0.80           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      (![X24 : $i, X25 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X24 @ X25)
% 0.58/0.80          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 0.58/0.80          | ~ (l1_pre_topc @ X25))),
% 0.58/0.80      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('6', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_E @ 
% 0.58/0.80        (k1_zfmisc_1 @ 
% 0.58/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t38_funct_2, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.80         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.58/0.80       ( ( r1_tarski @ C @ A ) =>
% 0.58/0.80         ( ( ( m1_subset_1 @
% 0.58/0.80               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.58/0.80               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.58/0.80             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.58/0.80             ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) ) | 
% 0.58/0.80           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.58/0.80  thf(zf_stmt_2, axiom,
% 0.58/0.80    (![B:$i,A:$i]:
% 0.58/0.80     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.58/0.80       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.80  thf(zf_stmt_4, axiom,
% 0.58/0.80    (![D:$i,C:$i,B:$i,A:$i]:
% 0.58/0.80     ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.58/0.80       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 0.58/0.80         ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.58/0.80         ( m1_subset_1 @
% 0.58/0.80           ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.58/0.80           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_5, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.80       ( ( r1_tarski @ C @ A ) =>
% 0.58/0.80         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ))).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.80         (~ (r1_tarski @ X14 @ X15)
% 0.58/0.80          | (zip_tseitin_1 @ X16 @ X15)
% 0.58/0.80          | ~ (v1_funct_1 @ X17)
% 0.58/0.80          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.58/0.80          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.58/0.80          | (zip_tseitin_0 @ X17 @ X14 @ X16 @ X15))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((zip_tseitin_0 @ sk_E @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.80           (u1_struct_0 @ sk_A))
% 0.58/0.80          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.80          | ~ (v1_funct_1 @ sk_E)
% 0.58/0.80          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((zip_tseitin_0 @ sk_E @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.80           (u1_struct_0 @ sk_A))
% 0.58/0.80          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | (zip_tseitin_0 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.58/0.80           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['6', '12'])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.80         ((m1_subset_1 @ (k2_partfun1 @ X8 @ X9 @ X10 @ X11) @ 
% 0.58/0.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 0.58/0.80          | ~ (zip_tseitin_0 @ X10 @ X11 @ X9 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | (m1_subset_1 @ 
% 0.58/0.80           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80            (u1_struct_0 @ sk_D)) @ 
% 0.58/0.80           (k1_zfmisc_1 @ 
% 0.58/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.80  thf(redefinition_r2_funct_2, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.80         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.80       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.58/0.80          | ~ (v1_funct_2 @ X4 @ X5 @ X6)
% 0.58/0.80          | ~ (v1_funct_1 @ X4)
% 0.58/0.80          | ~ (v1_funct_1 @ X7)
% 0.58/0.80          | ~ (v1_funct_2 @ X7 @ X5 @ X6)
% 0.58/0.80          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.58/0.80          | (r2_funct_2 @ X5 @ X6 @ X4 @ X7)
% 0.58/0.80          | ((X4) != (X7)))),
% 0.58/0.80      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.80         ((r2_funct_2 @ X5 @ X6 @ X7 @ X7)
% 0.58/0.80          | ~ (v1_funct_1 @ X7)
% 0.58/0.80          | ~ (v1_funct_2 @ X7 @ X5 @ X6)
% 0.58/0.80          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.58/0.80      inference('simplify', [status(thm)], ['16'])).
% 0.58/0.80  thf('18', plain,
% 0.58/0.80      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | ~ (v1_funct_2 @ 
% 0.58/0.80             (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.80              sk_E @ (u1_struct_0 @ sk_D)) @ 
% 0.58/0.80             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.80        | ~ (v1_funct_1 @ 
% 0.58/0.80             (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.80              sk_E @ (u1_struct_0 @ sk_D)))
% 0.58/0.80        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.80           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80            (u1_struct_0 @ sk_D)) @ 
% 0.58/0.80           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80            (u1_struct_0 @ sk_D))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['15', '17'])).
% 0.58/0.80  thf('19', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_E @ 
% 0.58/0.80        (k1_zfmisc_1 @ 
% 0.58/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(dt_k2_partfun1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.80       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.58/0.80         ( m1_subset_1 @
% 0.58/0.80           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.58/0.80           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.58/0.80  thf('20', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.58/0.80          | ~ (v1_funct_1 @ X0)
% 0.58/0.80          | (v1_funct_1 @ (k2_partfun1 @ X1 @ X2 @ X0 @ X3)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v1_funct_1 @ 
% 0.58/0.80           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80            X0))
% 0.58/0.80          | ~ (v1_funct_1 @ sk_E))),
% 0.58/0.80      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.80  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (v1_funct_1 @ 
% 0.58/0.80          (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80           X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | ~ (v1_funct_2 @ 
% 0.58/0.80             (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.80              sk_E @ (u1_struct_0 @ sk_D)) @ 
% 0.58/0.80             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.80        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.80           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80            (u1_struct_0 @ sk_D)) @ 
% 0.58/0.80           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80            (u1_struct_0 @ sk_D))))),
% 0.58/0.80      inference('demod', [status(thm)], ['18', '23'])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | (zip_tseitin_0 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.58/0.80           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['6', '12'])).
% 0.58/0.80  thf('26', plain,
% 0.58/0.80      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.80         ((v1_funct_2 @ (k2_partfun1 @ X8 @ X9 @ X10 @ X11) @ X11 @ X9)
% 0.58/0.80          | ~ (zip_tseitin_0 @ X10 @ X11 @ X9 @ X8))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.58/0.80  thf('27', plain,
% 0.58/0.80      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | (v1_funct_2 @ 
% 0.58/0.80           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80            (u1_struct_0 @ sk_D)) @ 
% 0.58/0.80           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      (((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.80         (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80          (u1_struct_0 @ sk_D)) @ 
% 0.58/0.80         (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.80          (u1_struct_0 @ sk_D)))
% 0.58/0.80        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('clc', [status(thm)], ['24', '27'])).
% 0.58/0.80  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_E @ 
% 0.58/0.80        (k1_zfmisc_1 @ 
% 0.58/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(d4_tmap_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.80             ( l1_pre_topc @ B ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.80                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                 ( m1_subset_1 @
% 0.58/0.80                   C @ 
% 0.58/0.80                   ( k1_zfmisc_1 @
% 0.58/0.80                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.80               ( ![D:$i]:
% 0.58/0.80                 ( ( m1_pre_topc @ D @ A ) =>
% 0.58/0.80                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.58/0.80                     ( k2_partfun1 @
% 0.58/0.80                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.58/0.81                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.81  thf('31', plain,
% 0.58/0.81      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.81         ((v2_struct_0 @ X20)
% 0.58/0.81          | ~ (v2_pre_topc @ X20)
% 0.58/0.81          | ~ (l1_pre_topc @ X20)
% 0.58/0.81          | ~ (m1_pre_topc @ X21 @ X22)
% 0.58/0.81          | ((k2_tmap_1 @ X22 @ X20 @ X23 @ X21)
% 0.58/0.81              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ 
% 0.58/0.81                 X23 @ (u1_struct_0 @ X21)))
% 0.58/0.81          | ~ (m1_subset_1 @ X23 @ 
% 0.58/0.81               (k1_zfmisc_1 @ 
% 0.58/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.58/0.81          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.58/0.81          | ~ (v1_funct_1 @ X23)
% 0.58/0.81          | ~ (l1_pre_topc @ X22)
% 0.58/0.81          | ~ (v2_pre_topc @ X22)
% 0.58/0.81          | (v2_struct_0 @ X22))),
% 0.58/0.81      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.58/0.81  thf('32', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v2_struct_0 @ sk_A)
% 0.58/0.81          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.81          | ~ (v1_funct_1 @ sk_E)
% 0.58/0.81          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.81          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.58/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81                 sk_E @ (u1_struct_0 @ X0)))
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.81          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.81          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.81          | (v2_struct_0 @ sk_B))),
% 0.58/0.81      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.81  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('35', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('36', plain,
% 0.58/0.81      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('38', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('39', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v2_struct_0 @ sk_A)
% 0.58/0.81          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.58/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81                 sk_E @ (u1_struct_0 @ X0)))
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.81          | (v2_struct_0 @ sk_B))),
% 0.58/0.81      inference('demod', [status(thm)],
% 0.58/0.81                ['32', '33', '34', '35', '36', '37', '38'])).
% 0.58/0.81  thf('40', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_B)
% 0.58/0.81        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.58/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81               sk_E @ (u1_struct_0 @ sk_D)))
% 0.58/0.81        | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['29', '39'])).
% 0.58/0.81  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('42', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_A)
% 0.58/0.81        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.58/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.58/0.81      inference('clc', [status(thm)], ['40', '41'])).
% 0.58/0.81  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('44', plain,
% 0.58/0.81      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.58/0.81         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.81            (u1_struct_0 @ sk_D)))),
% 0.58/0.81      inference('clc', [status(thm)], ['42', '43'])).
% 0.58/0.81  thf('45', plain,
% 0.58/0.81      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.58/0.81         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.81            (u1_struct_0 @ sk_D)))),
% 0.58/0.81      inference('clc', [status(thm)], ['42', '43'])).
% 0.58/0.81  thf('46', plain,
% 0.58/0.81      (((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.58/0.81         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.58/0.81        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['28', '44', '45'])).
% 0.58/0.81  thf('47', plain,
% 0.58/0.81      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81        | (v1_funct_2 @ 
% 0.58/0.81           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.81            (u1_struct_0 @ sk_D)) @ 
% 0.58/0.81           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.81  thf('48', plain,
% 0.58/0.81      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.58/0.81         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.81            (u1_struct_0 @ sk_D)))),
% 0.58/0.81      inference('clc', [status(thm)], ['42', '43'])).
% 0.58/0.81  thf('49', plain,
% 0.58/0.81      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.58/0.81           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.81      inference('demod', [status(thm)], ['47', '48'])).
% 0.58/0.81  thf('50', plain,
% 0.58/0.81      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81        | (m1_subset_1 @ 
% 0.58/0.81           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.81            (u1_struct_0 @ sk_D)) @ 
% 0.58/0.81           (k1_zfmisc_1 @ 
% 0.58/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.81  thf('51', plain,
% 0.58/0.81      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.58/0.81         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.81            (u1_struct_0 @ sk_D)))),
% 0.58/0.81      inference('clc', [status(thm)], ['42', '43'])).
% 0.58/0.81  thf('52', plain,
% 0.58/0.81      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81        | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.58/0.81           (k1_zfmisc_1 @ 
% 0.58/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.81      inference('demod', [status(thm)], ['50', '51'])).
% 0.58/0.81  thf(t77_tmap_1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.81             ( l1_pre_topc @ B ) ) =>
% 0.58/0.81           ( ![C:$i]:
% 0.58/0.81             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.81               ( ![D:$i]:
% 0.58/0.81                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.81                   ( ![E:$i]:
% 0.58/0.81                     ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.81                         ( v1_funct_2 @
% 0.58/0.81                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.81                         ( m1_subset_1 @
% 0.58/0.81                           E @ 
% 0.58/0.81                           ( k1_zfmisc_1 @
% 0.58/0.81                             ( k2_zfmisc_1 @
% 0.58/0.81                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.81                       ( ![F:$i]:
% 0.58/0.81                         ( ( ( v1_funct_1 @ F ) & 
% 0.58/0.81                             ( v1_funct_2 @
% 0.58/0.81                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.81                             ( m1_subset_1 @
% 0.58/0.81                               F @ 
% 0.58/0.81                               ( k1_zfmisc_1 @
% 0.58/0.81                                 ( k2_zfmisc_1 @
% 0.58/0.81                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.81                           ( ( ( r2_funct_2 @
% 0.58/0.81                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.81                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.58/0.81                               ( m1_pre_topc @ D @ C ) ) =>
% 0.58/0.81                             ( r2_funct_2 @
% 0.58/0.81                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.81                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 0.58/0.81                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.81  thf('53', plain,
% 0.58/0.81      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.81         ((v2_struct_0 @ X26)
% 0.58/0.81          | ~ (v2_pre_topc @ X26)
% 0.58/0.81          | ~ (l1_pre_topc @ X26)
% 0.58/0.81          | (v2_struct_0 @ X27)
% 0.58/0.81          | ~ (m1_pre_topc @ X27 @ X28)
% 0.58/0.81          | ~ (v1_funct_1 @ X29)
% 0.58/0.81          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X26))
% 0.58/0.81          | ~ (m1_subset_1 @ X29 @ 
% 0.58/0.81               (k1_zfmisc_1 @ 
% 0.58/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X26))))
% 0.58/0.81          | (r2_funct_2 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26) @ 
% 0.58/0.81             (k3_tmap_1 @ X28 @ X26 @ X30 @ X27 @ X29) @ 
% 0.58/0.81             (k2_tmap_1 @ X28 @ X26 @ X31 @ X27))
% 0.58/0.81          | ~ (r2_funct_2 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X26) @ X29 @ 
% 0.58/0.81               (k2_tmap_1 @ X28 @ X26 @ X31 @ X30))
% 0.58/0.81          | ~ (m1_pre_topc @ X27 @ X30)
% 0.58/0.81          | ~ (m1_subset_1 @ X31 @ 
% 0.58/0.81               (k1_zfmisc_1 @ 
% 0.58/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 0.58/0.81          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 0.58/0.81          | ~ (v1_funct_1 @ X31)
% 0.58/0.81          | ~ (m1_pre_topc @ X30 @ X28)
% 0.58/0.81          | (v2_struct_0 @ X30)
% 0.58/0.81          | ~ (l1_pre_topc @ X28)
% 0.58/0.81          | ~ (v2_pre_topc @ X28)
% 0.58/0.81          | (v2_struct_0 @ X28))),
% 0.58/0.81      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.58/0.81  thf('54', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81          | (v2_struct_0 @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | (v2_struct_0 @ sk_D)
% 0.58/0.81          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.58/0.81          | ~ (v1_funct_1 @ X1)
% 0.58/0.81          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.58/0.81          | ~ (m1_subset_1 @ X1 @ 
% 0.58/0.81               (k1_zfmisc_1 @ 
% 0.58/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.81          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.58/0.81          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.58/0.81               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.58/0.81          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.58/0.81              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.58/0.81          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.58/0.81               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.81          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.58/0.81          | ~ (m1_pre_topc @ X2 @ X0)
% 0.58/0.81          | (v2_struct_0 @ X2)
% 0.58/0.81          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.81          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.81          | (v2_struct_0 @ sk_B))),
% 0.58/0.81      inference('sup-', [status(thm)], ['52', '53'])).
% 0.58/0.81  thf('55', plain,
% 0.58/0.81      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.58/0.81         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.81            (u1_struct_0 @ sk_D)))),
% 0.58/0.81      inference('clc', [status(thm)], ['42', '43'])).
% 0.58/0.81  thf('56', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (v1_funct_1 @ 
% 0.58/0.81          (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.58/0.81           X0))),
% 0.58/0.81      inference('demod', [status(thm)], ['21', '22'])).
% 0.58/0.81  thf('57', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.58/0.81      inference('sup+', [status(thm)], ['55', '56'])).
% 0.58/0.81  thf('58', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('59', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('60', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81          | (v2_struct_0 @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | (v2_struct_0 @ sk_D)
% 0.58/0.81          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.58/0.81          | ~ (v1_funct_1 @ X1)
% 0.58/0.81          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.58/0.81          | ~ (m1_subset_1 @ X1 @ 
% 0.58/0.81               (k1_zfmisc_1 @ 
% 0.58/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.81          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.58/0.81          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.58/0.81               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.58/0.81          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.58/0.81              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.58/0.81          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.58/0.81               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.81          | ~ (m1_pre_topc @ X2 @ X0)
% 0.58/0.81          | (v2_struct_0 @ X2)
% 0.58/0.81          | (v2_struct_0 @ sk_B))),
% 0.58/0.81      inference('demod', [status(thm)], ['54', '57', '58', '59'])).
% 0.58/0.81  thf('61', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81          | (v2_struct_0 @ sk_B)
% 0.58/0.81          | (v2_struct_0 @ X0)
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ X1)
% 0.58/0.81          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.58/0.81              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 0.58/0.81          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.58/0.81               (k2_tmap_1 @ X1 @ sk_B @ X2 @ sk_D))
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.81          | ~ (m1_subset_1 @ X2 @ 
% 0.58/0.81               (k1_zfmisc_1 @ 
% 0.58/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.58/0.81          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.58/0.81          | ~ (v1_funct_1 @ X2)
% 0.58/0.81          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.58/0.81          | (v2_struct_0 @ sk_D)
% 0.58/0.81          | ~ (l1_pre_topc @ X1)
% 0.58/0.81          | ~ (v2_pre_topc @ X1)
% 0.58/0.81          | (v2_struct_0 @ X1)
% 0.58/0.81          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['49', '60'])).
% 0.58/0.81  thf('62', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((v2_struct_0 @ X1)
% 0.58/0.81          | ~ (v2_pre_topc @ X1)
% 0.58/0.81          | ~ (l1_pre_topc @ X1)
% 0.58/0.81          | (v2_struct_0 @ sk_D)
% 0.58/0.81          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.58/0.81          | ~ (v1_funct_1 @ X2)
% 0.58/0.81          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.58/0.81          | ~ (m1_subset_1 @ X2 @ 
% 0.58/0.81               (k1_zfmisc_1 @ 
% 0.58/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.81          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.58/0.81               (k2_tmap_1 @ X1 @ sk_B @ X2 @ sk_D))
% 0.58/0.81          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.58/0.81              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ X1)
% 0.58/0.81          | (v2_struct_0 @ X0)
% 0.58/0.81          | (v2_struct_0 @ sk_B)
% 0.58/0.81          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['61'])).
% 0.58/0.81  thf('63', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81          | (v2_struct_0 @ sk_B)
% 0.58/0.81          | (v2_struct_0 @ X0)
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.81          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.58/0.81              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.81          | ~ (m1_subset_1 @ sk_E @ 
% 0.58/0.81               (k1_zfmisc_1 @ 
% 0.58/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.58/0.81          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.81          | ~ (v1_funct_1 @ sk_E)
% 0.58/0.81          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.58/0.81          | (v2_struct_0 @ sk_D)
% 0.58/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.81          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.81          | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['46', '62'])).
% 0.58/0.81  thf('64', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_E @ 
% 0.58/0.81        (k1_zfmisc_1 @ 
% 0.58/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('65', plain,
% 0.58/0.81      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('67', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('70', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81          | (v2_struct_0 @ sk_B)
% 0.58/0.81          | (v2_struct_0 @ X0)
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.81          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.58/0.81              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.81          | (v2_struct_0 @ sk_D)
% 0.58/0.81          | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('demod', [status(thm)],
% 0.58/0.81                ['63', '64', '65', '66', '67', '68', '69'])).
% 0.58/0.81  thf('71', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v2_struct_0 @ sk_A)
% 0.58/0.81          | (v2_struct_0 @ sk_D)
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.81          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.58/0.81              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.58/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.81          | (v2_struct_0 @ X0)
% 0.58/0.81          | (v2_struct_0 @ sk_B)
% 0.58/0.81          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['70'])).
% 0.58/0.81  thf('72', plain,
% 0.58/0.81      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_C)
% 0.58/0.81        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.58/0.81        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.58/0.81            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.58/0.81        | (v2_struct_0 @ sk_D)
% 0.58/0.81        | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['1', '71'])).
% 0.58/0.81  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('74', plain,
% 0.58/0.81      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_C)
% 0.58/0.81        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.58/0.81            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.58/0.81        | (v2_struct_0 @ sk_D)
% 0.58/0.81        | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['72', '73'])).
% 0.58/0.81  thf('75', plain,
% 0.58/0.81      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.81          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.58/0.81           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.58/0.81          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('76', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_D)
% 0.58/0.81        | (v2_struct_0 @ sk_C)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['74', '75'])).
% 0.58/0.81  thf('77', plain,
% 0.58/0.81      (![X12 : $i, X13 : $i]:
% 0.58/0.81         (((X12) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X12 @ X13))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.81  thf('78', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_C)
% 0.58/0.81        | (v2_struct_0 @ sk_D)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['76', '77'])).
% 0.58/0.81  thf(fc2_struct_0, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.58/0.81       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.81  thf('79', plain,
% 0.58/0.81      (![X19 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.58/0.81          | ~ (l1_struct_0 @ X19)
% 0.58/0.81          | (v2_struct_0 @ X19))),
% 0.58/0.81      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.58/0.81  thf('80', plain,
% 0.58/0.81      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_D)
% 0.58/0.81        | (v2_struct_0 @ sk_C)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.81      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.81  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.81  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.81  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(dt_l1_pre_topc, axiom,
% 0.58/0.81    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.58/0.81  thf('83', plain,
% 0.58/0.81      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.58/0.81  thf('84', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.81      inference('sup-', [status(thm)], ['82', '83'])).
% 0.58/0.81  thf('85', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_D)
% 0.58/0.81        | (v2_struct_0 @ sk_C)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_B))),
% 0.58/0.81      inference('demod', [status(thm)], ['80', '81', '84'])).
% 0.58/0.81  thf('86', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_C)
% 0.58/0.81        | (v2_struct_0 @ sk_D)
% 0.58/0.81        | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('simplify', [status(thm)], ['85'])).
% 0.58/0.81  thf('87', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('88', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.58/0.81      inference('sup-', [status(thm)], ['86', '87'])).
% 0.58/0.81  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('90', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.58/0.81      inference('clc', [status(thm)], ['88', '89'])).
% 0.58/0.81  thf('91', plain, (~ (v2_struct_0 @ sk_C)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('92', plain, ((v2_struct_0 @ sk_D)),
% 0.58/0.81      inference('clc', [status(thm)], ['90', '91'])).
% 0.58/0.81  thf('93', plain, ($false), inference('demod', [status(thm)], ['0', '92'])).
% 0.58/0.81  
% 0.58/0.81  % SZS output end Refutation
% 0.58/0.81  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
