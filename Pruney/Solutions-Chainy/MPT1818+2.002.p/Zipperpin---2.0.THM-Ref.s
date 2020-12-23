%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8Sd5mc1e9g

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:09 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.50s
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

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

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

thf(t134_tmap_1,conjecture,(
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
                    & ( v1_tsep_1 @ D @ A )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( v1_tsep_1 @ E @ A )
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
                      & ( v1_tsep_1 @ D @ A )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( v1_tsep_1 @ E @ A )
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
    inference('cnf.neg',[status(esa)],[t134_tmap_1])).

thf('0',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_tsep_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_tsep_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_tsep_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( r4_tsep_1 @ A @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_tsep_1 @ X5 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( r4_tsep_1 @ X6 @ X5 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( v1_tsep_1 @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t88_tsep_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
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
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
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
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8Sd5mc1e9g
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:21:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 330 iterations in 0.206s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.67  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.67  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.67  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.67  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.45/0.67  thf(t134_tmap_1, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.67             ( l1_pre_topc @ B ) ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ![D:$i]:
% 0.45/0.67                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.45/0.67                     ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.67                   ( ![E:$i]:
% 0.45/0.67                     ( ( ( ~( v2_struct_0 @ E ) ) & ( v1_tsep_1 @ E @ A ) & 
% 0.45/0.67                         ( m1_pre_topc @ E @ A ) ) =>
% 0.45/0.67                       ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.45/0.67                         ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                             ( v1_funct_2 @
% 0.45/0.67                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                             ( v5_pre_topc @ C @ A @ B ) & 
% 0.45/0.67                             ( m1_subset_1 @
% 0.45/0.67                               C @ 
% 0.45/0.67                               ( k1_zfmisc_1 @
% 0.45/0.67                                 ( k2_zfmisc_1 @
% 0.45/0.67                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.45/0.67                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.45/0.67                             ( v1_funct_2 @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.45/0.67                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                             ( v5_pre_topc @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.45/0.67                             ( m1_subset_1 @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.45/0.67                               ( k1_zfmisc_1 @
% 0.45/0.67                                 ( k2_zfmisc_1 @
% 0.45/0.67                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.45/0.67                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.45/0.67                             ( v1_funct_2 @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.45/0.67                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                             ( v5_pre_topc @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.45/0.67                             ( m1_subset_1 @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.45/0.67                               ( k1_zfmisc_1 @
% 0.45/0.67                                 ( k2_zfmisc_1 @
% 0.45/0.67                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.67            ( l1_pre_topc @ A ) ) =>
% 0.45/0.67          ( ![B:$i]:
% 0.45/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.67                ( l1_pre_topc @ B ) ) =>
% 0.45/0.67              ( ![C:$i]:
% 0.45/0.67                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                    ( v1_funct_2 @
% 0.45/0.67                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                    ( m1_subset_1 @
% 0.45/0.67                      C @ 
% 0.45/0.67                      ( k1_zfmisc_1 @
% 0.45/0.67                        ( k2_zfmisc_1 @
% 0.45/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67                  ( ![D:$i]:
% 0.45/0.67                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.45/0.67                        ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.67                      ( ![E:$i]:
% 0.45/0.67                        ( ( ( ~( v2_struct_0 @ E ) ) & ( v1_tsep_1 @ E @ A ) & 
% 0.45/0.67                            ( m1_pre_topc @ E @ A ) ) =>
% 0.45/0.67                          ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.45/0.67                            ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                                ( v1_funct_2 @
% 0.45/0.67                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                                ( v5_pre_topc @ C @ A @ B ) & 
% 0.45/0.67                                ( m1_subset_1 @
% 0.45/0.67                                  C @ 
% 0.45/0.67                                  ( k1_zfmisc_1 @
% 0.45/0.67                                    ( k2_zfmisc_1 @
% 0.45/0.67                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.45/0.67                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.45/0.67                                ( v1_funct_2 @
% 0.45/0.67                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.45/0.67                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                                ( v5_pre_topc @
% 0.45/0.67                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.45/0.67                                ( m1_subset_1 @
% 0.45/0.67                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.45/0.67                                  ( k1_zfmisc_1 @
% 0.45/0.67                                    ( k2_zfmisc_1 @
% 0.45/0.67                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.45/0.67                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.45/0.67                                ( v1_funct_2 @
% 0.45/0.67                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.45/0.67                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                                ( v5_pre_topc @
% 0.45/0.67                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.45/0.67                                ( m1_subset_1 @
% 0.45/0.67                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.45/0.67                                  ( k1_zfmisc_1 @
% 0.45/0.67                                    ( k2_zfmisc_1 @
% 0.45/0.67                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t134_tmap_1])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.45/0.67        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.45/0.67       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('2', plain, ((v1_tsep_1 @ sk_E @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('3', plain, ((v1_tsep_1 @ sk_D @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t88_tsep_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.67               ( r4_tsep_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (v1_tsep_1 @ X5 @ X6)
% 0.45/0.67          | ~ (m1_pre_topc @ X5 @ X6)
% 0.45/0.67          | (r4_tsep_1 @ X6 @ X5 @ X7)
% 0.45/0.67          | ~ (m1_pre_topc @ X7 @ X6)
% 0.45/0.67          | ~ (v1_tsep_1 @ X7 @ X6)
% 0.45/0.67          | ~ (l1_pre_topc @ X6)
% 0.45/0.67          | ~ (v2_pre_topc @ X6)
% 0.45/0.67          | (v2_struct_0 @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t88_tsep_1])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_A)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ sk_D @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_A)
% 0.45/0.67          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | (r4_tsep_1 @ sk_A @ sk_D @ X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (((r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.45/0.67        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.45/0.67        | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['2', '9'])).
% 0.45/0.67  thf('11', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('12', plain, (((r4_tsep_1 @ sk_A @ sk_D @ sk_E) | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.67  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('14', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.45/0.67      inference('clc', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf('15', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.45/0.67        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('split', [status(esa)], ['16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t132_tmap_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.67             ( l1_pre_topc @ B ) ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ![D:$i]:
% 0.45/0.67                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.67                   ( ![E:$i]:
% 0.45/0.67                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.45/0.67                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 0.45/0.67                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 0.45/0.67                         ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                             ( v1_funct_2 @
% 0.45/0.67                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                             ( v5_pre_topc @ C @ A @ B ) & 
% 0.45/0.67                             ( m1_subset_1 @
% 0.45/0.67                               C @ 
% 0.45/0.67                               ( k1_zfmisc_1 @
% 0.45/0.67                                 ( k2_zfmisc_1 @
% 0.45/0.67                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.45/0.67                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.45/0.67                             ( v1_funct_2 @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.45/0.67                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                             ( v5_pre_topc @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.45/0.67                             ( m1_subset_1 @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.45/0.67                               ( k1_zfmisc_1 @
% 0.45/0.67                                 ( k2_zfmisc_1 @
% 0.45/0.67                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.45/0.67                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.45/0.67                             ( v1_funct_2 @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.45/0.67                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                             ( v5_pre_topc @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.45/0.67                             ( m1_subset_1 @
% 0.45/0.67                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.45/0.67                               ( k1_zfmisc_1 @
% 0.45/0.67                                 ( k2_zfmisc_1 @
% 0.45/0.67                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ X2)
% 0.45/0.67          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.45/0.67          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1) @ X1 @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X3)
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (l1_pre_topc @ X2)
% 0.45/0.67          | ~ (v2_pre_topc @ X2)
% 0.45/0.67          | (v2_struct_0 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [t132_tmap_1])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X2)
% 0.45/0.67          | ~ (v2_pre_topc @ X2)
% 0.45/0.67          | ~ (l1_pre_topc @ X2)
% 0.45/0.67          | (v2_struct_0 @ X3)
% 0.45/0.67          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.67          | (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1) @ X1 @ X0)
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.45/0.67          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.67          | (v2_struct_0 @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.45/0.67          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.45/0.67          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.45/0.67          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['18', '20'])).
% 0.45/0.67  thf('22', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | (v2_struct_0 @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.45/0.67          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.45/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.45/0.67          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['21', '22', '23', '24', '25', '26', '27'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      ((![X0 : $i, X1 : $i]:
% 0.45/0.67          ((v2_struct_0 @ sk_A)
% 0.45/0.67           | (v2_struct_0 @ X0)
% 0.45/0.67           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X1 @ sk_B)
% 0.45/0.67           | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.45/0.67           | ((sk_A) != (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.45/0.67           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67           | (v2_struct_0 @ X1)
% 0.45/0.67           | (v2_struct_0 @ sk_B)))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '28'])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          ((v2_struct_0 @ sk_B)
% 0.45/0.67           | (v2_struct_0 @ X0)
% 0.45/0.67           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67           | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ sk_E))
% 0.45/0.67           | ~ (r4_tsep_1 @ sk_A @ X0 @ sk_E)
% 0.45/0.67           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.45/0.67           | (v2_struct_0 @ sk_E)
% 0.45/0.67           | (v2_struct_0 @ sk_A)))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['15', '29'])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.45/0.67         | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ sk_E))
% 0.45/0.67         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '30'])).
% 0.45/0.67  thf('32', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('33', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.45/0.67         | ((sk_A) != (sk_A))
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_B)
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['34'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.45/0.67             sk_B)
% 0.45/0.67        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.45/0.67        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.45/0.67             sk_B)
% 0.45/0.67        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.45/0.67        | ~ (m1_subset_1 @ sk_C @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 0.45/0.67         <= (~
% 0.45/0.67             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.45/0.67               sk_B)))),
% 0.45/0.67      inference('split', [status(esa)], ['36'])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v2_struct_0 @ sk_B)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.45/0.67               sk_B)) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['35', '37'])).
% 0.45/0.67  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.45/0.67               sk_B)) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.67  thf('41', plain, (~ (v2_struct_0 @ sk_D)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.45/0.67               sk_B)) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['40', '41'])).
% 0.45/0.67  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_E))
% 0.45/0.67         <= (~
% 0.45/0.67             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.45/0.67               sk_B)) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['42', '43'])).
% 0.45/0.67  thf('45', plain, (~ (v2_struct_0 @ sk_E)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.45/0.67       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.45/0.67       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('split', [status(esa)], ['16'])).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('49', plain,
% 0.45/0.67      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.45/0.67       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('split', [status(esa)], ['48'])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.45/0.67       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('split', [status(esa)], ['50'])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.45/0.67        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.45/0.67       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('split', [status(esa)], ['52'])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.45/0.67       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('split', [status(esa)], ['54'])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.45/0.67        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.45/0.67       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('split', [status(esa)], ['56'])).
% 0.45/0.67  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('59', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.45/0.67      inference('split', [status(esa)], ['36'])).
% 0.45/0.67  thf('60', plain, (((v1_funct_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.67  thf('61', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('split', [status(esa)], ['36'])).
% 0.45/0.67  thf('63', plain,
% 0.45/0.67      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.67  thf('64', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('65', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ sk_C @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ sk_C @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.45/0.67      inference('split', [status(esa)], ['36'])).
% 0.45/0.67  thf('66', plain,
% 0.45/0.67      (((m1_subset_1 @ sk_C @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.67  thf('67', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.45/0.67      inference('clc', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf('68', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('69', plain,
% 0.45/0.67      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('split', [status(esa)], ['16'])).
% 0.45/0.67  thf('70', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('71', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ X2)
% 0.45/0.67          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.45/0.67          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X3)
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (l1_pre_topc @ X2)
% 0.45/0.67          | ~ (v2_pre_topc @ X2)
% 0.45/0.67          | (v2_struct_0 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [t132_tmap_1])).
% 0.45/0.67  thf('72', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X2)
% 0.45/0.67          | ~ (v2_pre_topc @ X2)
% 0.45/0.67          | ~ (l1_pre_topc @ X2)
% 0.45/0.67          | (v2_struct_0 @ X3)
% 0.45/0.67          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.67          | (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.45/0.67          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.67  thf('73', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.67          | (v2_struct_0 @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.45/0.67          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.45/0.67          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.45/0.67          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['70', '72'])).
% 0.45/0.67  thf('74', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('77', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('80', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | (v2_struct_0 @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.45/0.67          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.45/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.45/0.67          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['73', '74', '75', '76', '77', '78', '79'])).
% 0.45/0.67  thf('81', plain,
% 0.45/0.67      ((![X0 : $i, X1 : $i]:
% 0.45/0.67          ((v2_struct_0 @ sk_A)
% 0.45/0.67           | (v2_struct_0 @ X0)
% 0.45/0.67           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67           | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.45/0.67              (k1_zfmisc_1 @ 
% 0.45/0.67               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67           | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.45/0.67           | ((sk_A) != (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.45/0.67           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67           | (v2_struct_0 @ X1)
% 0.45/0.67           | (v2_struct_0 @ sk_B)))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['69', '80'])).
% 0.45/0.67  thf('82', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          ((v2_struct_0 @ sk_B)
% 0.45/0.67           | (v2_struct_0 @ X0)
% 0.45/0.67           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67           | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ sk_E))
% 0.45/0.67           | ~ (r4_tsep_1 @ sk_A @ X0 @ sk_E)
% 0.45/0.67           | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67              (k1_zfmisc_1 @ 
% 0.45/0.67               (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67           | (v2_struct_0 @ sk_E)
% 0.45/0.67           | (v2_struct_0 @ sk_A)))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['68', '81'])).
% 0.45/0.67  thf('83', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67            (k1_zfmisc_1 @ 
% 0.45/0.67             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67         | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ sk_E))
% 0.45/0.67         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['67', '82'])).
% 0.45/0.67  thf('84', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('85', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('86', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67            (k1_zfmisc_1 @ 
% 0.45/0.67             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67         | ((sk_A) != (sk_A))
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.45/0.67  thf('87', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_B)
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67            (k1_zfmisc_1 @ 
% 0.45/0.67             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['86'])).
% 0.45/0.67  thf('88', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.45/0.67      inference('split', [status(esa)], ['36'])).
% 0.45/0.67  thf('89', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v2_struct_0 @ sk_B)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['87', '88'])).
% 0.45/0.67  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('91', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['89', '90'])).
% 0.45/0.67  thf('92', plain, (~ (v2_struct_0 @ sk_D)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('93', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.67  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('95', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_E))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['93', '94'])).
% 0.45/0.67  thf('96', plain, (~ (v2_struct_0 @ sk_E)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('97', plain,
% 0.45/0.67      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.45/0.67       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['95', '96'])).
% 0.45/0.67  thf('98', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.45/0.67      inference('clc', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf('99', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('100', plain,
% 0.45/0.67      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('split', [status(esa)], ['16'])).
% 0.45/0.67  thf('101', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('102', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ X2)
% 0.45/0.67          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.45/0.67          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X3)
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (l1_pre_topc @ X2)
% 0.45/0.67          | ~ (v2_pre_topc @ X2)
% 0.45/0.67          | (v2_struct_0 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [t132_tmap_1])).
% 0.45/0.67  thf('103', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X2)
% 0.45/0.67          | ~ (v2_pre_topc @ X2)
% 0.45/0.67          | ~ (l1_pre_topc @ X2)
% 0.45/0.67          | (v2_struct_0 @ X3)
% 0.45/0.67          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.67          | (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.45/0.67          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['102'])).
% 0.45/0.67  thf('104', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.67          | (v2_struct_0 @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.45/0.67          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.45/0.67          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.45/0.67          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['101', '103'])).
% 0.45/0.67  thf('105', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('108', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('111', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | (v2_struct_0 @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.45/0.67          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.45/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.45/0.67          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['104', '105', '106', '107', '108', '109', '110'])).
% 0.45/0.67  thf('112', plain,
% 0.45/0.67      ((![X0 : $i, X1 : $i]:
% 0.45/0.67          ((v2_struct_0 @ sk_A)
% 0.45/0.67           | (v2_struct_0 @ X0)
% 0.45/0.67           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67           | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.45/0.67              (k1_zfmisc_1 @ 
% 0.45/0.67               (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67           | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.45/0.67           | ((sk_A) != (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.45/0.67           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67           | (v2_struct_0 @ X1)
% 0.45/0.67           | (v2_struct_0 @ sk_B)))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['100', '111'])).
% 0.45/0.67  thf('113', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          ((v2_struct_0 @ sk_B)
% 0.45/0.67           | (v2_struct_0 @ X0)
% 0.45/0.67           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67           | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ sk_E))
% 0.45/0.67           | ~ (r4_tsep_1 @ sk_A @ X0 @ sk_E)
% 0.45/0.67           | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.45/0.67              (k1_zfmisc_1 @ 
% 0.45/0.67               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67           | (v2_struct_0 @ sk_E)
% 0.45/0.67           | (v2_struct_0 @ sk_A)))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['99', '112'])).
% 0.45/0.67  thf('114', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67            (k1_zfmisc_1 @ 
% 0.45/0.67             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67         | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ sk_E))
% 0.45/0.67         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['98', '113'])).
% 0.45/0.67  thf('115', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('116', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('117', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67            (k1_zfmisc_1 @ 
% 0.45/0.67             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67         | ((sk_A) != (sk_A))
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.45/0.67  thf('118', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_B)
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67            (k1_zfmisc_1 @ 
% 0.45/0.67             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['117'])).
% 0.45/0.67  thf('119', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.45/0.67      inference('split', [status(esa)], ['36'])).
% 0.45/0.67  thf('120', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_E)
% 0.45/0.67         | (v2_struct_0 @ sk_D)
% 0.45/0.67         | (v2_struct_0 @ sk_B)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['118', '119'])).
% 0.45/0.67  thf('121', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('122', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['120', '121'])).
% 0.45/0.67  thf('123', plain, (~ (v2_struct_0 @ sk_D)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('124', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['122', '123'])).
% 0.45/0.67  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('126', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_E))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.45/0.67             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['124', '125'])).
% 0.45/0.67  thf('127', plain, (~ (v2_struct_0 @ sk_E)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('128', plain,
% 0.45/0.67      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.45/0.67       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['126', '127'])).
% 0.45/0.67  thf('129', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.45/0.67      inference('clc', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf('130', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('131', plain,
% 0.45/0.67      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.45/0.67         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.67      inference('split', [status(esa)], ['16'])).
% 0.45/0.67  thf('132', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('133', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ X2)
% 0.45/0.67          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.45/0.67          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3) @ 
% 0.45/0.67             (u1_struct_0 @ X3) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X3)
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (l1_pre_topc @ X2)
% 0.45/0.67          | ~ (v2_pre_topc @ X2)
% 0.45/0.67          | (v2_struct_0 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [t132_tmap_1])).
% 0.45/0.67  thf('134', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X2)
% 0.45/0.67          | ~ (v2_pre_topc @ X2)
% 0.45/0.67          | ~ (l1_pre_topc @ X2)
% 0.45/0.67          | (v2_struct_0 @ X3)
% 0.45/0.67          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.67          | (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3) @ 
% 0.45/0.67             (u1_struct_0 @ X3) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (m1_subset_1 @ X4 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.45/0.67          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v1_funct_1 @ X4)
% 0.45/0.67          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.45/0.67          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['133'])).
% 0.45/0.67  thf('135', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.67          | (v2_struct_0 @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.45/0.67          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.45/0.67          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.45/0.67          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.45/0.67             (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['132', '134'])).
% 0.45/0.67  thf('136', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('137', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('139', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('141', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('142', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | (v2_struct_0 @ X0)
% 0.45/0.67          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.67          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.45/0.67          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.45/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.45/0.67          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.45/0.67             (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.45/0.67          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ X1)
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.68                ['135', '136', '137', '138', '139', '140', '141'])).
% 0.45/0.68  thf('143', plain,
% 0.45/0.68      ((![X0 : $i, X1 : $i]:
% 0.45/0.68          ((v2_struct_0 @ sk_A)
% 0.45/0.68           | (v2_struct_0 @ X0)
% 0.45/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.68           | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.45/0.68              (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.45/0.68           | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.45/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.45/0.68           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.45/0.68           | (v2_struct_0 @ X1)
% 0.45/0.68           | (v2_struct_0 @ sk_B)))
% 0.45/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['131', '142'])).
% 0.45/0.68  thf('144', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          ((v2_struct_0 @ sk_B)
% 0.45/0.68           | (v2_struct_0 @ X0)
% 0.45/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ sk_E))
% 0.45/0.68           | ~ (r4_tsep_1 @ sk_A @ X0 @ sk_E)
% 0.45/0.68           | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.45/0.68           | (v2_struct_0 @ sk_E)
% 0.45/0.68           | (v2_struct_0 @ sk_A)))
% 0.45/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['130', '143'])).
% 0.45/0.68  thf('145', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A)
% 0.45/0.68         | (v2_struct_0 @ sk_E)
% 0.45/0.68         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.45/0.68         | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ sk_E))
% 0.45/0.68         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.45/0.68         | (v2_struct_0 @ sk_D)
% 0.45/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['129', '144'])).
% 0.45/0.68  thf('146', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('147', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('148', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A)
% 0.45/0.68         | (v2_struct_0 @ sk_E)
% 0.45/0.68         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.45/0.68         | ((sk_A) != (sk_A))
% 0.45/0.68         | (v2_struct_0 @ sk_D)
% 0.45/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.45/0.68  thf('149', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_B)
% 0.45/0.68         | (v2_struct_0 @ sk_D)
% 0.45/0.68         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.45/0.68         | (v2_struct_0 @ sk_E)
% 0.45/0.68         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['148'])).
% 0.45/0.68  thf('150', plain,
% 0.45/0.68      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('split', [status(esa)], ['36'])).
% 0.45/0.68  thf('151', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A)
% 0.45/0.68         | (v2_struct_0 @ sk_E)
% 0.45/0.68         | (v2_struct_0 @ sk_D)
% 0.45/0.68         | (v2_struct_0 @ sk_B)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.45/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['149', '150'])).
% 0.45/0.68  thf('152', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('153', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.45/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['151', '152'])).
% 0.45/0.68  thf('154', plain, (~ (v2_struct_0 @ sk_D)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('155', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.45/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['153', '154'])).
% 0.45/0.68  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('157', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_E))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.45/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['155', '156'])).
% 0.45/0.68  thf('158', plain, (~ (v2_struct_0 @ sk_E)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('159', plain,
% 0.45/0.68      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.45/0.68       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['157', '158'])).
% 0.45/0.68  thf('160', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.45/0.68      inference('clc', [status(thm)], ['12', '13'])).
% 0.45/0.68  thf('161', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('162', plain,
% 0.50/0.68      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('split', [status(esa)], ['16'])).
% 0.50/0.68  thf('163', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_C @ 
% 0.50/0.68        (k1_zfmisc_1 @ 
% 0.50/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('164', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.68         ((v2_struct_0 @ X0)
% 0.50/0.68          | ~ (v2_pre_topc @ X0)
% 0.50/0.68          | ~ (l1_pre_topc @ X0)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ X2)
% 0.50/0.68          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.50/0.68          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3) @ X3 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.68          | (v2_struct_0 @ X3)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (l1_pre_topc @ X2)
% 0.50/0.68          | ~ (v2_pre_topc @ X2)
% 0.50/0.68          | (v2_struct_0 @ X2))),
% 0.50/0.68      inference('cnf', [status(esa)], [t132_tmap_1])).
% 0.50/0.68  thf('165', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.68         ((v2_struct_0 @ X2)
% 0.50/0.68          | ~ (v2_pre_topc @ X2)
% 0.50/0.68          | ~ (l1_pre_topc @ X2)
% 0.50/0.68          | (v2_struct_0 @ X3)
% 0.50/0.68          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.68          | (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3) @ X3 @ X0)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.50/0.68          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ X2)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (l1_pre_topc @ X0)
% 0.50/0.68          | ~ (v2_pre_topc @ X0)
% 0.50/0.68          | (v2_struct_0 @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['164'])).
% 0.50/0.68  thf('166', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v2_struct_0 @ sk_B)
% 0.50/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.68          | (v2_struct_0 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.50/0.68          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.50/0.68          | ~ (v1_funct_1 @ sk_C)
% 0.50/0.68          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.68          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X1 @ sk_B)
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.50/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['163', '165'])).
% 0.50/0.68  thf('167', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('168', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('170', plain,
% 0.50/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('172', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('173', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v2_struct_0 @ sk_B)
% 0.50/0.68          | (v2_struct_0 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.50/0.68          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.50/0.68          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X1 @ sk_B)
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | (v2_struct_0 @ sk_A))),
% 0.50/0.68      inference('demod', [status(thm)],
% 0.50/0.68                ['166', '167', '168', '169', '170', '171', '172'])).
% 0.50/0.68  thf('174', plain,
% 0.50/0.68      ((![X0 : $i, X1 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.50/0.68           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X1)
% 0.50/0.68           | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['162', '173'])).
% 0.50/0.68  thf('175', plain,
% 0.50/0.68      ((![X0 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_B)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ sk_E))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ X0 @ sk_E)
% 0.50/0.68           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68              sk_B)
% 0.50/0.68           | (v2_struct_0 @ sk_E)
% 0.50/0.68           | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['161', '174'])).
% 0.50/0.68  thf('176', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.50/0.68         | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ sk_E))
% 0.50/0.68         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['160', '175'])).
% 0.50/0.68  thf('177', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('178', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('179', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.50/0.68         | ((sk_A) != (sk_A))
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.50/0.68  thf('180', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['179'])).
% 0.50/0.68  thf('181', plain,
% 0.50/0.68      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)))),
% 0.50/0.68      inference('split', [status(esa)], ['36'])).
% 0.50/0.68  thf('182', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['180', '181'])).
% 0.50/0.68  thf('183', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('184', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['182', '183'])).
% 0.50/0.68  thf('185', plain, (~ (v2_struct_0 @ sk_D)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('186', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('clc', [status(thm)], ['184', '185'])).
% 0.50/0.68  thf('187', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('188', plain,
% 0.50/0.68      (((v2_struct_0 @ sk_E))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('clc', [status(thm)], ['186', '187'])).
% 0.50/0.68  thf('189', plain, (~ (v2_struct_0 @ sk_E)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('190', plain,
% 0.50/0.68      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.50/0.68       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['188', '189'])).
% 0.50/0.68  thf('191', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.50/0.68      inference('clc', [status(thm)], ['12', '13'])).
% 0.50/0.68  thf('192', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('193', plain,
% 0.50/0.68      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('split', [status(esa)], ['16'])).
% 0.50/0.68  thf('194', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_C @ 
% 0.50/0.68        (k1_zfmisc_1 @ 
% 0.50/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('195', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.68         ((v2_struct_0 @ X0)
% 0.50/0.68          | ~ (v2_pre_topc @ X0)
% 0.50/0.68          | ~ (l1_pre_topc @ X0)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ X2)
% 0.50/0.68          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.50/0.68          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1) @ 
% 0.50/0.68             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.68          | (v2_struct_0 @ X3)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (l1_pre_topc @ X2)
% 0.50/0.68          | ~ (v2_pre_topc @ X2)
% 0.50/0.68          | (v2_struct_0 @ X2))),
% 0.50/0.68      inference('cnf', [status(esa)], [t132_tmap_1])).
% 0.50/0.68  thf('196', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.68         ((v2_struct_0 @ X2)
% 0.50/0.68          | ~ (v2_pre_topc @ X2)
% 0.50/0.68          | ~ (l1_pre_topc @ X2)
% 0.50/0.68          | (v2_struct_0 @ X3)
% 0.50/0.68          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.68          | (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1) @ 
% 0.50/0.68             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.50/0.68          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ X2)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (l1_pre_topc @ X0)
% 0.50/0.68          | ~ (v2_pre_topc @ X0)
% 0.50/0.68          | (v2_struct_0 @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['195'])).
% 0.50/0.68  thf('197', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v2_struct_0 @ sk_B)
% 0.50/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.68          | (v2_struct_0 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.50/0.68          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.50/0.68          | ~ (v1_funct_1 @ sk_C)
% 0.50/0.68          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.68          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.50/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['194', '196'])).
% 0.50/0.68  thf('198', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('199', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('201', plain,
% 0.50/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('202', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('203', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('204', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v2_struct_0 @ sk_B)
% 0.50/0.68          | (v2_struct_0 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.50/0.68          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.50/0.68          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | (v2_struct_0 @ sk_A))),
% 0.50/0.68      inference('demod', [status(thm)],
% 0.50/0.68                ['197', '198', '199', '200', '201', '202', '203'])).
% 0.50/0.68  thf('205', plain,
% 0.50/0.68      ((![X0 : $i, X1 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.50/0.68              (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.50/0.68           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X1)
% 0.50/0.68           | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['193', '204'])).
% 0.50/0.68  thf('206', plain,
% 0.50/0.68      ((![X0 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_B)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ sk_E))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ X0 @ sk_E)
% 0.50/0.68           | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68              (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | (v2_struct_0 @ sk_E)
% 0.50/0.68           | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['192', '205'])).
% 0.50/0.68  thf('207', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.50/0.68         | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ sk_E))
% 0.50/0.68         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['191', '206'])).
% 0.50/0.68  thf('208', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('209', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('210', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.50/0.68         | ((sk_A) != (sk_A))
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['207', '208', '209'])).
% 0.50/0.68  thf('211', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['210'])).
% 0.50/0.68  thf('212', plain,
% 0.50/0.68      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.68      inference('split', [status(esa)], ['36'])).
% 0.50/0.68  thf('213', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['211', '212'])).
% 0.50/0.68  thf('214', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('215', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['213', '214'])).
% 0.50/0.68  thf('216', plain, (~ (v2_struct_0 @ sk_D)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('217', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('clc', [status(thm)], ['215', '216'])).
% 0.50/0.68  thf('218', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('219', plain,
% 0.50/0.68      (((v2_struct_0 @ sk_E))
% 0.50/0.68         <= (~
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('clc', [status(thm)], ['217', '218'])).
% 0.50/0.68  thf('220', plain, (~ (v2_struct_0 @ sk_E)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('221', plain,
% 0.50/0.68      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.50/0.68       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['219', '220'])).
% 0.50/0.68  thf('222', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.50/0.68      inference('clc', [status(thm)], ['12', '13'])).
% 0.50/0.68  thf('223', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('224', plain,
% 0.50/0.68      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('split', [status(esa)], ['16'])).
% 0.50/0.68  thf('225', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_C @ 
% 0.50/0.68        (k1_zfmisc_1 @ 
% 0.50/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('226', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.68         ((v2_struct_0 @ X0)
% 0.50/0.68          | ~ (v2_pre_topc @ X0)
% 0.50/0.68          | ~ (l1_pre_topc @ X0)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ X2)
% 0.50/0.68          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.50/0.68          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3))
% 0.50/0.68          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.68          | (v2_struct_0 @ X3)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (l1_pre_topc @ X2)
% 0.50/0.68          | ~ (v2_pre_topc @ X2)
% 0.50/0.68          | (v2_struct_0 @ X2))),
% 0.50/0.68      inference('cnf', [status(esa)], [t132_tmap_1])).
% 0.50/0.68  thf('227', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.68         ((v2_struct_0 @ X2)
% 0.50/0.68          | ~ (v2_pre_topc @ X2)
% 0.50/0.68          | ~ (l1_pre_topc @ X2)
% 0.50/0.68          | (v2_struct_0 @ X3)
% 0.50/0.68          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.68          | (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3))
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.50/0.68          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ X2)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (l1_pre_topc @ X0)
% 0.50/0.68          | ~ (v2_pre_topc @ X0)
% 0.50/0.68          | (v2_struct_0 @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['226'])).
% 0.50/0.68  thf('228', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v2_struct_0 @ sk_B)
% 0.50/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.68          | (v2_struct_0 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.50/0.68          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.50/0.68          | ~ (v1_funct_1 @ sk_C)
% 0.50/0.68          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.68          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.50/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['225', '227'])).
% 0.50/0.68  thf('229', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('230', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('231', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('232', plain,
% 0.50/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('233', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('234', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('235', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v2_struct_0 @ sk_B)
% 0.50/0.68          | (v2_struct_0 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.50/0.68          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.50/0.68          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | (v2_struct_0 @ sk_A))),
% 0.50/0.68      inference('demod', [status(thm)],
% 0.50/0.68                ['228', '229', '230', '231', '232', '233', '234'])).
% 0.50/0.68  thf('236', plain,
% 0.50/0.68      ((![X0 : $i, X1 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.50/0.68           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X1)
% 0.50/0.68           | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['224', '235'])).
% 0.50/0.68  thf('237', plain,
% 0.50/0.68      ((![X0 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_B)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ sk_E))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ X0 @ sk_E)
% 0.50/0.68           | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68           | (v2_struct_0 @ sk_E)
% 0.50/0.68           | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['223', '236'])).
% 0.50/0.68  thf('238', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68         | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ sk_E))
% 0.50/0.68         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['222', '237'])).
% 0.50/0.68  thf('239', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('240', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('241', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68         | ((sk_A) != (sk_A))
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['238', '239', '240'])).
% 0.50/0.68  thf('242', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['241'])).
% 0.50/0.68  thf('243', plain,
% 0.50/0.68      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.50/0.68      inference('split', [status(esa)], ['36'])).
% 0.50/0.68  thf('244', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['242', '243'])).
% 0.50/0.68  thf('245', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('246', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['244', '245'])).
% 0.50/0.68  thf('247', plain, (~ (v2_struct_0 @ sk_D)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('248', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('clc', [status(thm)], ['246', '247'])).
% 0.50/0.68  thf('249', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('250', plain,
% 0.50/0.68      (((v2_struct_0 @ sk_E))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('clc', [status(thm)], ['248', '249'])).
% 0.50/0.68  thf('251', plain, (~ (v2_struct_0 @ sk_E)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('252', plain,
% 0.50/0.68      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.50/0.68       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['250', '251'])).
% 0.50/0.68  thf('253', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.50/0.68      inference('clc', [status(thm)], ['12', '13'])).
% 0.50/0.68  thf('254', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('255', plain,
% 0.50/0.68      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('split', [status(esa)], ['16'])).
% 0.50/0.68  thf('256', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_C @ 
% 0.50/0.68        (k1_zfmisc_1 @ 
% 0.50/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('257', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.68         ((v2_struct_0 @ X0)
% 0.50/0.68          | ~ (v2_pre_topc @ X0)
% 0.50/0.68          | ~ (l1_pre_topc @ X0)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ X2)
% 0.50/0.68          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.50/0.68          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1))
% 0.50/0.68          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.68          | (v2_struct_0 @ X3)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (l1_pre_topc @ X2)
% 0.50/0.68          | ~ (v2_pre_topc @ X2)
% 0.50/0.68          | (v2_struct_0 @ X2))),
% 0.50/0.68      inference('cnf', [status(esa)], [t132_tmap_1])).
% 0.50/0.68  thf('258', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.68         ((v2_struct_0 @ X2)
% 0.50/0.68          | ~ (v2_pre_topc @ X2)
% 0.50/0.68          | ~ (l1_pre_topc @ X2)
% 0.50/0.68          | (v2_struct_0 @ X3)
% 0.50/0.68          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.68          | (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1))
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v5_pre_topc @ X4 @ X2 @ X0)
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.50/0.68          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ X2)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (l1_pre_topc @ X0)
% 0.50/0.68          | ~ (v2_pre_topc @ X0)
% 0.50/0.68          | (v2_struct_0 @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['257'])).
% 0.50/0.68  thf('259', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v2_struct_0 @ sk_B)
% 0.50/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.68          | (v2_struct_0 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.50/0.68          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.50/0.68          | ~ (v1_funct_1 @ sk_C)
% 0.50/0.68          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.68          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.50/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['256', '258'])).
% 0.50/0.68  thf('260', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('261', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('263', plain,
% 0.50/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('264', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('265', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('266', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((v2_struct_0 @ sk_B)
% 0.50/0.68          | (v2_struct_0 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68          | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ X1))
% 0.50/0.68          | ~ (r4_tsep_1 @ sk_A @ X0 @ X1)
% 0.50/0.68          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | (v2_struct_0 @ sk_A))),
% 0.50/0.68      inference('demod', [status(thm)],
% 0.50/0.68                ['259', '260', '261', '262', '263', '264', '265'])).
% 0.50/0.68  thf('267', plain,
% 0.50/0.68      ((![X0 : $i, X1 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X1 @ X0))
% 0.50/0.68           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X1)
% 0.50/0.68           | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['255', '266'])).
% 0.50/0.68  thf('268', plain,
% 0.50/0.68      ((![X0 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_B)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ X0 @ sk_E))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ X0 @ sk_E)
% 0.50/0.68           | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.50/0.68           | (v2_struct_0 @ sk_E)
% 0.50/0.68           | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['254', '267'])).
% 0.50/0.68  thf('269', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.50/0.68         | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ sk_E))
% 0.50/0.68         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['253', '268'])).
% 0.50/0.68  thf('270', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('271', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('272', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.50/0.68         | ((sk_A) != (sk_A))
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['269', '270', '271'])).
% 0.50/0.68  thf('273', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['272'])).
% 0.50/0.68  thf('274', plain,
% 0.50/0.68      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.50/0.68      inference('split', [status(esa)], ['36'])).
% 0.50/0.68  thf('275', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['273', '274'])).
% 0.50/0.68  thf('276', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('277', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['275', '276'])).
% 0.50/0.68  thf('278', plain, (~ (v2_struct_0 @ sk_D)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('279', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('clc', [status(thm)], ['277', '278'])).
% 0.50/0.68  thf('280', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('281', plain,
% 0.50/0.68      (((v2_struct_0 @ sk_E))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('clc', [status(thm)], ['279', '280'])).
% 0.50/0.68  thf('282', plain, (~ (v2_struct_0 @ sk_E)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('283', plain,
% 0.50/0.68      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.50/0.68       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['281', '282'])).
% 0.50/0.68  thf('284', plain,
% 0.50/0.68      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.50/0.68       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.50/0.68       ~ ((v1_funct_1 @ sk_C)) | 
% 0.50/0.68       ~ ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))) | 
% 0.50/0.68       ~
% 0.50/0.68       ((m1_subset_1 @ sk_C @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))) | 
% 0.50/0.68       ~
% 0.50/0.68       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.50/0.68       ~
% 0.50/0.68       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.50/0.68       ~
% 0.50/0.68       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.50/0.68       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.50/0.68       ~
% 0.50/0.68       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.50/0.68       ~
% 0.50/0.68       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.50/0.68       ~
% 0.50/0.68       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.50/0.68      inference('split', [status(esa)], ['36'])).
% 0.50/0.68  thf('285', plain,
% 0.50/0.68      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68        | (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('286', plain,
% 0.50/0.68      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.50/0.68         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.50/0.68      inference('split', [status(esa)], ['285'])).
% 0.50/0.68  thf('287', plain,
% 0.50/0.68      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.50/0.68        | (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('288', plain,
% 0.50/0.68      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.50/0.68         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)))),
% 0.50/0.68      inference('split', [status(esa)], ['287'])).
% 0.50/0.68  thf('289', plain,
% 0.50/0.68      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.50/0.68        | (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('290', plain,
% 0.50/0.68      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.68      inference('split', [status(esa)], ['289'])).
% 0.50/0.68  thf('291', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.50/0.68        | (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('292', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.50/0.68         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('split', [status(esa)], ['291'])).
% 0.50/0.68  thf('293', plain,
% 0.50/0.68      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.50/0.68        | (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('294', plain,
% 0.50/0.68      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.50/0.68         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.50/0.68      inference('split', [status(esa)], ['293'])).
% 0.50/0.68  thf('295', plain,
% 0.50/0.68      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.50/0.68        | (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('296', plain,
% 0.50/0.68      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 0.50/0.68         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)))),
% 0.50/0.68      inference('split', [status(esa)], ['295'])).
% 0.50/0.68  thf('297', plain,
% 0.50/0.68      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.50/0.68        | (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('298', plain,
% 0.50/0.68      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.68      inference('split', [status(esa)], ['297'])).
% 0.50/0.68  thf('299', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.50/0.68        | (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('300', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.50/0.68         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('split', [status(esa)], ['299'])).
% 0.50/0.68  thf('301', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.68         ((v2_struct_0 @ X0)
% 0.50/0.68          | ~ (v2_pre_topc @ X0)
% 0.50/0.68          | ~ (l1_pre_topc @ X0)
% 0.50/0.68          | (v2_struct_0 @ X1)
% 0.50/0.68          | ~ (m1_pre_topc @ X1 @ X2)
% 0.50/0.68          | ((X2) != (k1_tsep_1 @ X2 @ X1 @ X3))
% 0.50/0.68          | ~ (r4_tsep_1 @ X2 @ X1 @ X3)
% 0.50/0.68          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1))
% 0.50/0.68          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1) @ 
% 0.50/0.68               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1) @ X1 @ X0)
% 0.50/0.68          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X1) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3))
% 0.50/0.68          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3) @ 
% 0.50/0.68               (u1_struct_0 @ X3) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3) @ X3 @ X0)
% 0.50/0.68          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X4 @ X3) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | (v5_pre_topc @ X4 @ X2 @ X0)
% 0.50/0.68          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.68          | (v2_struct_0 @ X3)
% 0.50/0.68          | ~ (m1_subset_1 @ X4 @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.50/0.68          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X4)
% 0.50/0.68          | ~ (l1_pre_topc @ X2)
% 0.50/0.68          | ~ (v2_pre_topc @ X2)
% 0.50/0.68          | (v2_struct_0 @ X2))),
% 0.50/0.68      inference('cnf', [status(esa)], [t132_tmap_1])).
% 0.50/0.68  thf('302', plain,
% 0.50/0.68      ((![X0 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_A)
% 0.50/0.68           | ~ (v2_pre_topc @ sk_A)
% 0.50/0.68           | ~ (l1_pre_topc @ sk_A)
% 0.50/0.68           | ~ (v1_funct_1 @ sk_C)
% 0.50/0.68           | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | ~ (m1_subset_1 @ sk_C @ 
% 0.50/0.68                (k1_zfmisc_1 @ 
% 0.50/0.68                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (k1_zfmisc_1 @ 
% 0.50/0.68                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.50/0.68           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.50/0.68           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.50/0.68           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68                sk_B)
% 0.50/0.68           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ X0))
% 0.50/0.68           | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ sk_D)
% 0.50/0.68           | ~ (l1_pre_topc @ sk_B)
% 0.50/0.68           | ~ (v2_pre_topc @ sk_B)
% 0.50/0.68           | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['300', '301'])).
% 0.50/0.68  thf('303', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('304', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('305', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('306', plain,
% 0.50/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('307', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_C @ 
% 0.50/0.68        (k1_zfmisc_1 @ 
% 0.50/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('308', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('309', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('310', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('311', plain,
% 0.50/0.68      ((![X0 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (k1_zfmisc_1 @ 
% 0.50/0.68                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.50/0.68           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.50/0.68           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.50/0.68           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68                sk_B)
% 0.50/0.68           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ X0))
% 0.50/0.68           | (v2_struct_0 @ sk_D)
% 0.50/0.68           | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('demod', [status(thm)],
% 0.50/0.68                ['302', '303', '304', '305', '306', '307', '308', '309', '310'])).
% 0.50/0.68  thf('312', plain,
% 0.50/0.68      ((![X0 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_B)
% 0.50/0.68           | (v2_struct_0 @ sk_D)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ X0))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.50/0.68           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.50/0.68           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68                sk_B)
% 0.50/0.68           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.50/0.68           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.50/0.68           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (k1_zfmisc_1 @ 
% 0.50/0.68                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.50/0.68           | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['298', '311'])).
% 0.50/0.68  thf('313', plain,
% 0.50/0.68      ((![X0 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (k1_zfmisc_1 @ 
% 0.50/0.68                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.50/0.68           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.50/0.68           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.50/0.68           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ X0))
% 0.50/0.68           | (v2_struct_0 @ sk_D)
% 0.50/0.68           | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['296', '312'])).
% 0.50/0.68  thf('314', plain,
% 0.50/0.68      ((![X0 : $i]:
% 0.50/0.68          ((v2_struct_0 @ sk_B)
% 0.50/0.68           | (v2_struct_0 @ sk_D)
% 0.50/0.68           | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ X0))
% 0.50/0.68           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.50/0.68           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.50/0.68           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.50/0.68           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.50/0.68           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.50/0.68                (k1_zfmisc_1 @ 
% 0.50/0.68                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.50/0.68           | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.50/0.68           | (v2_struct_0 @ X0)
% 0.50/0.68           | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['294', '313'])).
% 0.50/0.68  thf('315', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.50/0.68         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68              sk_B)
% 0.50/0.68         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.50/0.68         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.50/0.68         | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_D @ sk_E))
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['292', '314'])).
% 0.50/0.68  thf('316', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('317', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.50/0.68      inference('clc', [status(thm)], ['12', '13'])).
% 0.50/0.68  thf('318', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('319', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68              sk_B)
% 0.50/0.68         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.50/0.68         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68         | ((sk_A) != (sk_A))
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('demod', [status(thm)], ['315', '316', '317', '318'])).
% 0.50/0.68  thf('320', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.50/0.68         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68              sk_B)
% 0.50/0.68         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('simplify', [status(thm)], ['319'])).
% 0.50/0.68  thf('321', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68              sk_B)
% 0.50/0.68         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['290', '320'])).
% 0.50/0.68  thf('322', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.50/0.68         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['288', '321'])).
% 0.50/0.68  thf('323', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_B)))
% 0.50/0.68         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['286', '322'])).
% 0.50/0.68  thf('324', plain,
% 0.50/0.68      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.50/0.68         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.50/0.68      inference('split', [status(esa)], ['36'])).
% 0.50/0.68  thf('325', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_B)
% 0.50/0.68         | (v2_struct_0 @ sk_D)
% 0.50/0.68         | (v2_struct_0 @ sk_E)
% 0.50/0.68         | (v2_struct_0 @ sk_A)))
% 0.50/0.68         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.50/0.68             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['323', '324'])).
% 0.50/0.68  thf('326', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('327', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.50/0.68         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.50/0.68             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['325', '326'])).
% 0.50/0.68  thf('328', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('329', plain,
% 0.50/0.68      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.50/0.68         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.50/0.68             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('clc', [status(thm)], ['327', '328'])).
% 0.50/0.68  thf('330', plain, (~ (v2_struct_0 @ sk_D)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('331', plain,
% 0.50/0.68      (((v2_struct_0 @ sk_E))
% 0.50/0.68         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.50/0.68             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.50/0.68             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.50/0.68             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.50/0.68             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.50/0.68               sk_B)) & 
% 0.50/0.68             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68               (k1_zfmisc_1 @ 
% 0.50/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.50/0.68      inference('clc', [status(thm)], ['329', '330'])).
% 0.50/0.68  thf('332', plain, (~ (v2_struct_0 @ sk_E)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('333', plain,
% 0.50/0.68      (~
% 0.50/0.68       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.50/0.68       ~
% 0.50/0.68       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.50/0.68       ~
% 0.50/0.68       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.50/0.68       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.50/0.68       ~
% 0.50/0.68       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.50/0.68       ~
% 0.50/0.68       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.50/0.68       ~
% 0.50/0.68       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.50/0.68         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.50/0.68       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.50/0.68       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['331', '332'])).
% 0.50/0.68  thf('334', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.50/0.68        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('335', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.50/0.68       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.50/0.68      inference('split', [status(esa)], ['334'])).
% 0.50/0.68  thf('336', plain, ($false),
% 0.50/0.68      inference('sat_resolution*', [status(thm)],
% 0.50/0.68                ['1', '46', '47', '49', '51', '53', '55', '57', '60', '63', 
% 0.50/0.68                 '66', '97', '128', '159', '190', '221', '252', '283', '284', 
% 0.50/0.68                 '333', '335'])).
% 0.50/0.68  
% 0.50/0.68  % SZS output end Refutation
% 0.50/0.68  
% 0.50/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
