%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1817+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VztFAxDVJF

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:20 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  361 ( 949 expanded)
%              Number of leaves         :   23 ( 267 expanded)
%              Depth                    :   20
%              Number of atoms          : 7097 (75017 expanded)
%              Number of equality atoms :   84 ( 548 expanded)
%              Maximal formula depth    :   31 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(t133_tmap_1,conjecture,(
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
                    & ( v1_borsuk_1 @ D @ A )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( v1_borsuk_1 @ E @ A )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( A
                          = ( k1_tsep_1 @ A @ D @ E ) )
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
                      & ( v1_borsuk_1 @ D @ A )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( v1_borsuk_1 @ E @ A )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
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
    inference('cnf.neg',[status(esa)],[t133_tmap_1])).

thf('0',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_borsuk_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_borsuk_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_borsuk_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_borsuk_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( r4_tsep_1 @ A @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_borsuk_1 @ X5 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( r4_tsep_1 @ X6 @ X5 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( v1_borsuk_1 @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t87_tsep_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('10',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_tmap_1,axiom,(
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

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t132_tmap_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27'])).

thf('29',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X1 @ sk_B )
        | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X0 @ sk_E ) )
        | ~ ( r4_tsep_1 @ sk_A @ X0 @ sk_E )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ( v2_struct_0 @ sk_E )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','29'])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','30'])).

thf('32',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( sk_A != sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
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

thf('37',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('48',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['36'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['12','13'])).

thf('68',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t132_tmap_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78','79'])).

thf('81',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X0 @ sk_E ) )
        | ~ ( r4_tsep_1 @ sk_A @ X0 @ sk_E )
        | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v2_struct_0 @ sk_E )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['68','81'])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','82'])).

thf('84',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( sk_A != sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['12','13'])).

thf('99',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t132_tmap_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108','109','110'])).

thf('112',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['100','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X0 @ sk_E ) )
        | ~ ( r4_tsep_1 @ sk_A @ X0 @ sk_E )
        | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v2_struct_0 @ sk_E )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['99','112'])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['98','113'])).

thf('115',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( sk_A != sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['12','13'])).

thf('130',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t132_tmap_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140','141'])).

thf('143',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['131','142'])).

thf('144',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X0 @ sk_E ) )
        | ~ ( r4_tsep_1 @ sk_A @ X0 @ sk_E )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
        | ( v2_struct_0 @ sk_E )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['130','143'])).

thf('145',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['129','144'])).

thf('146',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_A != sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['12','13'])).

thf('161',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) @ X3 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t132_tmap_1])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','165'])).

thf('167',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170','171','172'])).

thf('174',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['162','173'])).

thf('175',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X0 @ sk_E ) )
        | ~ ( r4_tsep_1 @ sk_A @ X0 @ sk_E )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
        | ( v2_struct_0 @ sk_E )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['161','174'])).

thf('176',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['160','175'])).

thf('177',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( sk_A != sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('182',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['12','13'])).

thf('192',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t132_tmap_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','196'])).

thf('198',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198','199','200','201','202','203'])).

thf('205',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['193','204'])).

thf('206',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X0 @ sk_E ) )
        | ~ ( r4_tsep_1 @ sk_A @ X0 @ sk_E )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ( v2_struct_0 @ sk_E )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['192','205'])).

thf('207',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['191','206'])).

thf('208',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_A != sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('213',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['217','218'])).

thf('220',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['12','13'])).

thf('223',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('225',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t132_tmap_1])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['225','227'])).

thf('229',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['228','229','230','231','232','233','234'])).

thf('236',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['224','235'])).

thf('237',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X0 @ sk_E ) )
        | ~ ( r4_tsep_1 @ sk_A @ X0 @ sk_E )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
        | ( v2_struct_0 @ sk_E )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['223','236'])).

thf('238',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['222','237'])).

thf('239',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_A != sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['36'])).

thf('244',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['246','247'])).

thf('249',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['12','13'])).

thf('254',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('256',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t132_tmap_1])).

thf('258',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['256','258'])).

thf('260',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ X0 @ X1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['259','260','261','262','263','264','265'])).

thf('267',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) )
        | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['255','266'])).

thf('268',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ X0 @ sk_E ) )
        | ~ ( r4_tsep_1 @ sk_A @ X0 @ sk_E )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ( v2_struct_0 @ sk_E )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['254','267'])).

thf('269',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['253','268'])).

thf('270',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( sk_A != sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['269','270','271'])).

thf('273',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['36'])).

thf('275',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['277','278'])).

thf('280',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('285',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['285'])).

thf('287',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['287'])).

thf('289',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['289'])).

thf('291',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['291'])).

thf('293',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['293'])).

thf('295',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['295'])).

thf('297',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['297'])).

thf('299',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['299'])).

thf('301',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X1 @ X3 ) )
      | ~ ( r4_tsep_1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) @ X3 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X4 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ X4 @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t132_tmap_1])).

thf('302',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) )
        | ~ ( m1_pre_topc @ sk_D @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['302','303','304','305','306','307','308','309','310'])).

thf('312',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['298','311'])).

thf('313',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['296','312'])).

thf('314',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D )
        | ( sk_A
         != ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['294','313'])).

thf('315',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['292','314'])).

thf('316',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['12','13'])).

thf('318',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_A != sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['315','316','317','318'])).

thf('320',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['290','320'])).

thf('322',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['288','321'])).

thf('323',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['286','322'])).

thf('324',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('325',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['327','328'])).

thf('330',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['329','330'])).

thf('332',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['331','332'])).

thf('334',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['334'])).

thf('336',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','49','51','53','55','57','60','63','66','97','128','159','190','221','252','283','284','333','335'])).


%------------------------------------------------------------------------------
