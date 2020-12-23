%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KzgePNIQeG

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:50 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  231 ( 950 expanded)
%              Number of leaves         :   34 ( 277 expanded)
%              Depth                    :   30
%              Number of atoms          : 2767 (34581 expanded)
%              Number of equality atoms :   13 ( 450 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t66_tmap_1,conjecture,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( v3_pre_topc @ E @ B )
                                  & ( r2_hidden @ F @ E )
                                  & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ( ( ( v3_pre_topc @ E @ B )
                                    & ( r2_hidden @ F @ E )
                                    & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                    & ( F = G ) )
                                 => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                  <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tmap_1])).

thf('0',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( m1_connsp_2 @ E @ B @ F )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_tarski @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_connsp_2 @ X22 @ X19 @ X21 )
      | ( X21 != X23 )
      | ~ ( r1_tmap_1 @ X19 @ X24 @ X25 @ X21 )
      | ( r1_tmap_1 @ X20 @ X24 @ ( k2_tmap_1 @ X19 @ X24 @ X25 @ X20 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('21',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( r1_tmap_1 @ X20 @ X24 @ ( k2_tmap_1 @ X19 @ X24 @ X25 @ X20 ) @ X23 )
      | ~ ( r1_tmap_1 @ X19 @ X24 @ X25 @ X23 )
      | ~ ( m1_connsp_2 @ X22 @ X19 @ X23 )
      | ~ ( r1_tarski @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X1 )
      | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k1_tops_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_E @ sk_E )
    | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference(demod,[status(thm)],['45','47'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ sk_G @ ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_tops_1 @ X11 @ X12 ) )
      | ( m1_connsp_2 @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('60',plain,
    ( ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['31','34','62'])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['13','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['8'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('77',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_connsp_2 @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 @ X16 )
      | ~ ( m1_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ sk_E @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ sk_E @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G )
    | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['60','61'])).

thf('86',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['60','61'])).

thf('90',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ sk_E @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ sk_E @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('98',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['88','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['14'])).

thf('112',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_tarski @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_connsp_2 @ X22 @ X19 @ X21 )
      | ( X21 != X23 )
      | ~ ( r1_tmap_1 @ X20 @ X24 @ ( k2_tmap_1 @ X19 @ X24 @ X25 @ X20 ) @ X23 )
      | ( r1_tmap_1 @ X19 @ X24 @ X25 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('114',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( r1_tmap_1 @ X19 @ X24 @ X25 @ X23 )
      | ~ ( r1_tmap_1 @ X20 @ X24 @ ( k2_tmap_1 @ X19 @ X24 @ X25 @ X20 ) @ X23 )
      | ~ ( m1_connsp_2 @ X22 @ X19 @ X23 )
      | ~ ( r1_tarski @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119','120','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
        | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference('sup-',[status(thm)],['111','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('126',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
        | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ sk_G )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference('sup-',[status(thm)],['110','127'])).

thf('129',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('130',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['86','87'])).

thf('131',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('132',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r1_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X18 )
      | ~ ( m1_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['130','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('139',plain,
    ( ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['129','143'])).

thf('145',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('146',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['60','61'])).

thf('147',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r1_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X18 )
      | ~ ( m1_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ sk_E @ X0 @ sk_B ) @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ sk_E @ X0 @ sk_B ) @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('155',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_E ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_E )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['145','159'])).

thf('161',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('166',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['144','169'])).

thf('171',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('172',plain,
    ( ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['86','87'])).

thf('175',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('176',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_connsp_2 @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 @ X16 )
      | ~ ( m1_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['174','180'])).

thf('182',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('183',plain,
    ( ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(demod,[status(thm)],['128','173','185'])).

thf('187',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('188',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['3','12','75','76','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KzgePNIQeG
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 193 iterations in 0.129s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.60  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.60  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.36/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.36/0.60  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.36/0.60  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.36/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.60  thf(t66_tmap_1, conjecture,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.60             ( l1_pre_topc @ B ) ) =>
% 0.36/0.60           ( ![C:$i]:
% 0.36/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.60                 ( m1_subset_1 @
% 0.36/0.60                   C @ 
% 0.36/0.60                   ( k1_zfmisc_1 @
% 0.36/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.60               ( ![D:$i]:
% 0.36/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.60                   ( ![E:$i]:
% 0.36/0.60                     ( ( m1_subset_1 @
% 0.36/0.60                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.60                       ( ![F:$i]:
% 0.36/0.60                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.60                           ( ![G:$i]:
% 0.36/0.60                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.60                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.36/0.60                                   ( r2_hidden @ F @ E ) & 
% 0.36/0.60                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.36/0.60                                   ( ( F ) = ( G ) ) ) =>
% 0.36/0.60                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.36/0.60                                   ( r1_tmap_1 @
% 0.36/0.60                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i]:
% 0.36/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.60            ( l1_pre_topc @ A ) ) =>
% 0.36/0.60          ( ![B:$i]:
% 0.36/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.60                ( l1_pre_topc @ B ) ) =>
% 0.36/0.60              ( ![C:$i]:
% 0.36/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.60                    ( v1_funct_2 @
% 0.36/0.60                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.60                    ( m1_subset_1 @
% 0.36/0.60                      C @ 
% 0.36/0.60                      ( k1_zfmisc_1 @
% 0.36/0.60                        ( k2_zfmisc_1 @
% 0.36/0.60                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.60                  ( ![D:$i]:
% 0.36/0.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.60                      ( ![E:$i]:
% 0.36/0.60                        ( ( m1_subset_1 @
% 0.36/0.60                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.60                          ( ![F:$i]:
% 0.36/0.60                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.60                              ( ![G:$i]:
% 0.36/0.60                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.60                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.36/0.60                                      ( r2_hidden @ F @ E ) & 
% 0.36/0.60                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.36/0.60                                      ( ( F ) = ( G ) ) ) =>
% 0.36/0.60                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.36/0.60                                      ( r1_tmap_1 @
% 0.36/0.60                                        D @ A @ 
% 0.36/0.60                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.36/0.60        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('1', plain, (((sk_F) = (sk_G))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.36/0.60        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.36/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (~
% 0.36/0.60       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) | 
% 0.36/0.60       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.36/0.60      inference('split', [status(esa)], ['2'])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.36/0.60        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('5', plain, (((sk_F) = (sk_G))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.36/0.60        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.36/0.60      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.36/0.60      inference('split', [status(esa)], ['6'])).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.36/0.60        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('9', plain,
% 0.36/0.60      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.36/0.60         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('split', [status(esa)], ['8'])).
% 0.36/0.60  thf('10', plain, (((sk_F) = (sk_G))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.36/0.60         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)) | 
% 0.36/0.60       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.36/0.60      inference('sup-', [status(thm)], ['7', '11'])).
% 0.36/0.60  thf('13', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.36/0.60        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('split', [status(esa)], ['14'])).
% 0.36/0.60  thf('16', plain, (((sk_F) = (sk_G))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('19', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t65_tmap_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.60             ( l1_pre_topc @ B ) ) =>
% 0.36/0.60           ( ![C:$i]:
% 0.36/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.60                 ( m1_subset_1 @
% 0.36/0.60                   C @ 
% 0.36/0.60                   ( k1_zfmisc_1 @
% 0.36/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.60               ( ![D:$i]:
% 0.36/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.60                   ( ![E:$i]:
% 0.36/0.60                     ( ( m1_subset_1 @
% 0.36/0.60                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.60                       ( ![F:$i]:
% 0.36/0.60                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.60                           ( ![G:$i]:
% 0.36/0.60                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.60                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.36/0.60                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.36/0.60                                   ( ( F ) = ( G ) ) ) =>
% 0.36/0.60                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.36/0.60                                   ( r1_tmap_1 @
% 0.36/0.60                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.60         ((v2_struct_0 @ X19)
% 0.36/0.60          | ~ (v2_pre_topc @ X19)
% 0.36/0.60          | ~ (l1_pre_topc @ X19)
% 0.36/0.60          | (v2_struct_0 @ X20)
% 0.36/0.60          | ~ (m1_pre_topc @ X20 @ X19)
% 0.36/0.60          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 0.36/0.60          | ~ (r1_tarski @ X22 @ (u1_struct_0 @ X20))
% 0.36/0.60          | ~ (m1_connsp_2 @ X22 @ X19 @ X21)
% 0.36/0.60          | ((X21) != (X23))
% 0.36/0.60          | ~ (r1_tmap_1 @ X19 @ X24 @ X25 @ X21)
% 0.36/0.60          | (r1_tmap_1 @ X20 @ X24 @ (k2_tmap_1 @ X19 @ X24 @ X25 @ X20) @ X23)
% 0.36/0.60          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 0.36/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.60          | ~ (m1_subset_1 @ X25 @ 
% 0.36/0.60               (k1_zfmisc_1 @ 
% 0.36/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))))
% 0.36/0.60          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))
% 0.36/0.60          | ~ (v1_funct_1 @ X25)
% 0.36/0.60          | ~ (l1_pre_topc @ X24)
% 0.36/0.60          | ~ (v2_pre_topc @ X24)
% 0.36/0.60          | (v2_struct_0 @ X24))),
% 0.36/0.60      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      (![X19 : $i, X20 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.60         ((v2_struct_0 @ X24)
% 0.36/0.60          | ~ (v2_pre_topc @ X24)
% 0.36/0.60          | ~ (l1_pre_topc @ X24)
% 0.36/0.60          | ~ (v1_funct_1 @ X25)
% 0.36/0.60          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))
% 0.36/0.60          | ~ (m1_subset_1 @ X25 @ 
% 0.36/0.60               (k1_zfmisc_1 @ 
% 0.36/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))))
% 0.36/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.60          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 0.36/0.60          | (r1_tmap_1 @ X20 @ X24 @ (k2_tmap_1 @ X19 @ X24 @ X25 @ X20) @ X23)
% 0.36/0.60          | ~ (r1_tmap_1 @ X19 @ X24 @ X25 @ X23)
% 0.36/0.60          | ~ (m1_connsp_2 @ X22 @ X19 @ X23)
% 0.36/0.60          | ~ (r1_tarski @ X22 @ (u1_struct_0 @ X20))
% 0.36/0.60          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 0.36/0.60          | ~ (m1_pre_topc @ X20 @ X19)
% 0.36/0.60          | (v2_struct_0 @ X20)
% 0.36/0.60          | ~ (l1_pre_topc @ X19)
% 0.36/0.60          | ~ (v2_pre_topc @ X19)
% 0.36/0.60          | (v2_struct_0 @ X19))),
% 0.36/0.60      inference('simplify', [status(thm)], ['20'])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | (v2_struct_0 @ X0)
% 0.36/0.60          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.36/0.60          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.60          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.36/0.60          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.36/0.60          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.36/0.60             X1)
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60               (u1_struct_0 @ sk_A))
% 0.36/0.60          | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.60          | (v2_struct_0 @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['19', '21'])).
% 0.36/0.60  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('26', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | (v2_struct_0 @ X0)
% 0.36/0.60          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.36/0.60          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.60          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.36/0.60          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.36/0.60          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.36/0.60             X1)
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | (v2_struct_0 @ sk_A))),
% 0.36/0.60      inference('demod', [status(thm)],
% 0.36/0.60                ['22', '23', '24', '25', '26', '27', '28'])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_A)
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.60          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.36/0.60             X1)
% 0.36/0.60          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.36/0.60          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X1)
% 0.36/0.60          | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.36/0.60          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.60          | (v2_struct_0 @ X0)
% 0.36/0.60          | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['18', '29'])).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((v2_struct_0 @ sk_B)
% 0.36/0.60           | (v2_struct_0 @ X0)
% 0.36/0.60           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.60           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.36/0.60           | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.36/0.60           | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.36/0.60           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.36/0.60              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_G)
% 0.36/0.60           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.36/0.60           | (v2_struct_0 @ sk_A)))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['17', '30'])).
% 0.36/0.60  thf('32', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('33', plain, (((sk_F) = (sk_G))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('34', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('35', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('36', plain, (((sk_F) = (sk_G))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('37', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.36/0.60      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t56_tops_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_pre_topc @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60           ( ![C:$i]:
% 0.36/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.60                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.60  thf('40', plain,
% 0.36/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.36/0.60          | ~ (v3_pre_topc @ X7 @ X8)
% 0.36/0.60          | ~ (r1_tarski @ X7 @ X9)
% 0.36/0.60          | (r1_tarski @ X7 @ (k1_tops_1 @ X8 @ X9))
% 0.36/0.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.36/0.60          | ~ (l1_pre_topc @ X8))),
% 0.36/0.60      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.36/0.60  thf('41', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.36/0.60          | ~ (r1_tarski @ sk_E @ X0)
% 0.36/0.60          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.60  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('43', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.36/0.60          | ~ (r1_tarski @ sk_E @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.36/0.60  thf('45', plain,
% 0.36/0.60      ((~ (r1_tarski @ sk_E @ sk_E)
% 0.36/0.60        | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['38', '44'])).
% 0.36/0.60  thf(d10_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.60  thf('46', plain,
% 0.36/0.60      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('47', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.36/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.60  thf('48', plain, ((r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E))),
% 0.36/0.60      inference('demod', [status(thm)], ['45', '47'])).
% 0.36/0.60  thf(d3_tarski, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.60          | (r2_hidden @ X0 @ X2)
% 0.36/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('50', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.36/0.60          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.36/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.60  thf('51', plain, ((r2_hidden @ sk_G @ (k1_tops_1 @ sk_B @ sk_E))),
% 0.36/0.60      inference('sup-', [status(thm)], ['37', '50'])).
% 0.36/0.60  thf('52', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(d1_connsp_2, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.60           ( ![C:$i]:
% 0.36/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.60                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.60  thf('53', plain,
% 0.36/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.36/0.60          | ~ (r2_hidden @ X10 @ (k1_tops_1 @ X11 @ X12))
% 0.36/0.60          | (m1_connsp_2 @ X12 @ X11 @ X10)
% 0.36/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.36/0.60          | ~ (l1_pre_topc @ X11)
% 0.36/0.60          | ~ (v2_pre_topc @ X11)
% 0.36/0.60          | (v2_struct_0 @ X11))),
% 0.36/0.60      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.60  thf('54', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.60  thf('55', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('56', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('57', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.36/0.60  thf('58', plain,
% 0.36/0.60      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.36/0.60        | (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['51', '57'])).
% 0.36/0.60  thf('59', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('60', plain,
% 0.36/0.60      (((m1_connsp_2 @ sk_E @ sk_B @ sk_G) | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.60  thf('61', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('62', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.36/0.60      inference('clc', [status(thm)], ['60', '61'])).
% 0.36/0.60  thf('63', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((v2_struct_0 @ sk_B)
% 0.36/0.60           | (v2_struct_0 @ X0)
% 0.36/0.60           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.60           | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.36/0.60           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.36/0.60              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_G)
% 0.36/0.60           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.36/0.60           | (v2_struct_0 @ sk_A)))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('demod', [status(thm)], ['31', '34', '62'])).
% 0.36/0.60  thf('64', plain,
% 0.36/0.60      ((((v2_struct_0 @ sk_A)
% 0.36/0.60         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))
% 0.36/0.60         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.36/0.60         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.36/0.60         | (v2_struct_0 @ sk_D_1)
% 0.36/0.60         | (v2_struct_0 @ sk_B)))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['13', '63'])).
% 0.36/0.60  thf('65', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('66', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('67', plain,
% 0.36/0.60      ((((v2_struct_0 @ sk_A)
% 0.36/0.60         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.36/0.60         | (v2_struct_0 @ sk_D_1)
% 0.36/0.60         | (v2_struct_0 @ sk_B)))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.36/0.60  thf('68', plain,
% 0.36/0.60      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))
% 0.36/0.60         <= (~
% 0.36/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.36/0.60      inference('split', [status(esa)], ['8'])).
% 0.36/0.60  thf('69', plain,
% 0.36/0.60      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_A)))
% 0.36/0.60         <= (~
% 0.36/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) & 
% 0.36/0.60             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.60  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('71', plain,
% 0.36/0.60      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1)))
% 0.36/0.60         <= (~
% 0.36/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) & 
% 0.36/0.60             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('clc', [status(thm)], ['69', '70'])).
% 0.36/0.60  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('73', plain,
% 0.36/0.60      (((v2_struct_0 @ sk_D_1))
% 0.36/0.60         <= (~
% 0.36/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) & 
% 0.36/0.60             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.36/0.60      inference('clc', [status(thm)], ['71', '72'])).
% 0.36/0.60  thf('74', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('75', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) | 
% 0.36/0.60       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.36/0.60      inference('sup-', [status(thm)], ['73', '74'])).
% 0.36/0.60  thf('76', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) | 
% 0.36/0.60       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.36/0.60      inference('split', [status(esa)], ['6'])).
% 0.36/0.60  thf('77', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('78', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t7_connsp_2, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.60           ( ![C:$i]:
% 0.36/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.36/0.60                    ( ![D:$i]:
% 0.36/0.60                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.36/0.60                          ( m1_subset_1 @
% 0.36/0.60                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.60                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.36/0.60                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.60  thf('79', plain,
% 0.36/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.36/0.60          | (m1_connsp_2 @ (sk_D @ X18 @ X16 @ X17) @ X17 @ X16)
% 0.36/0.60          | ~ (m1_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.60          | ~ (l1_pre_topc @ X17)
% 0.36/0.60          | ~ (v2_pre_topc @ X17)
% 0.36/0.60          | (v2_struct_0 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.36/0.60  thf('80', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.36/0.60          | (m1_connsp_2 @ (sk_D @ sk_E @ X0 @ sk_B) @ sk_B @ X0)
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.36/0.60  thf('81', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('83', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.36/0.60          | (m1_connsp_2 @ (sk_D @ sk_E @ X0 @ sk_B) @ sk_B @ X0)
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.36/0.60  thf('84', plain,
% 0.36/0.60      (((m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)
% 0.36/0.60        | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['77', '83'])).
% 0.36/0.60  thf('85', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.36/0.60      inference('clc', [status(thm)], ['60', '61'])).
% 0.36/0.60  thf('86', plain,
% 0.36/0.60      (((m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['84', '85'])).
% 0.36/0.60  thf('87', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('88', plain, ((m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)),
% 0.36/0.60      inference('clc', [status(thm)], ['86', '87'])).
% 0.36/0.60  thf('89', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.36/0.60      inference('clc', [status(thm)], ['60', '61'])).
% 0.36/0.60  thf('90', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('91', plain,
% 0.36/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.36/0.60          | (m1_subset_1 @ (sk_D @ X18 @ X16 @ X17) @ 
% 0.36/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.60          | ~ (m1_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.60          | ~ (l1_pre_topc @ X17)
% 0.36/0.60          | ~ (v2_pre_topc @ X17)
% 0.36/0.60          | (v2_struct_0 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.36/0.60  thf('92', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.36/0.60          | (m1_subset_1 @ (sk_D @ sk_E @ X0 @ sk_B) @ 
% 0.36/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['90', '91'])).
% 0.36/0.60  thf('93', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('95', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.36/0.60          | (m1_subset_1 @ (sk_D @ sk_E @ X0 @ sk_B) @ 
% 0.36/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.36/0.60  thf('96', plain,
% 0.36/0.60      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.36/0.60        | (m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.36/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['89', '95'])).
% 0.36/0.60  thf('97', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('98', plain,
% 0.36/0.60      (((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.36/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['96', '97'])).
% 0.36/0.60  thf('99', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('100', plain,
% 0.36/0.60      ((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.36/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('clc', [status(thm)], ['98', '99'])).
% 0.36/0.60  thf('101', plain,
% 0.36/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.36/0.60          | (m1_subset_1 @ (sk_D @ X18 @ X16 @ X17) @ 
% 0.36/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.60          | ~ (m1_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.60          | ~ (l1_pre_topc @ X17)
% 0.36/0.60          | ~ (v2_pre_topc @ X17)
% 0.36/0.60          | (v2_struct_0 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.36/0.60  thf('102', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.36/0.60          | (m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.36/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['100', '101'])).
% 0.36/0.60  thf('103', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('104', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('105', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.36/0.60          | (m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.36/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.36/0.60  thf('106', plain,
% 0.36/0.60      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.36/0.60        | (m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['88', '105'])).
% 0.36/0.60  thf('107', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('108', plain,
% 0.36/0.60      (((m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['106', '107'])).
% 0.36/0.60  thf('109', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('110', plain,
% 0.36/0.60      ((m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('clc', [status(thm)], ['108', '109'])).
% 0.36/0.60  thf('111', plain,
% 0.36/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.36/0.60      inference('split', [status(esa)], ['14'])).
% 0.36/0.60  thf('112', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('113', plain,
% 0.36/0.60      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.60         ((v2_struct_0 @ X19)
% 0.36/0.60          | ~ (v2_pre_topc @ X19)
% 0.36/0.60          | ~ (l1_pre_topc @ X19)
% 0.36/0.60          | (v2_struct_0 @ X20)
% 0.36/0.60          | ~ (m1_pre_topc @ X20 @ X19)
% 0.36/0.60          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 0.36/0.60          | ~ (r1_tarski @ X22 @ (u1_struct_0 @ X20))
% 0.36/0.60          | ~ (m1_connsp_2 @ X22 @ X19 @ X21)
% 0.36/0.60          | ((X21) != (X23))
% 0.36/0.60          | ~ (r1_tmap_1 @ X20 @ X24 @ (k2_tmap_1 @ X19 @ X24 @ X25 @ X20) @ 
% 0.36/0.60               X23)
% 0.36/0.60          | (r1_tmap_1 @ X19 @ X24 @ X25 @ X21)
% 0.36/0.60          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 0.36/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.60          | ~ (m1_subset_1 @ X25 @ 
% 0.36/0.60               (k1_zfmisc_1 @ 
% 0.36/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))))
% 0.36/0.60          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))
% 0.36/0.60          | ~ (v1_funct_1 @ X25)
% 0.36/0.60          | ~ (l1_pre_topc @ X24)
% 0.36/0.60          | ~ (v2_pre_topc @ X24)
% 0.36/0.60          | (v2_struct_0 @ X24))),
% 0.36/0.60      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.36/0.60  thf('114', plain,
% 0.36/0.60      (![X19 : $i, X20 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.60         ((v2_struct_0 @ X24)
% 0.36/0.60          | ~ (v2_pre_topc @ X24)
% 0.36/0.60          | ~ (l1_pre_topc @ X24)
% 0.36/0.60          | ~ (v1_funct_1 @ X25)
% 0.36/0.60          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))
% 0.36/0.60          | ~ (m1_subset_1 @ X25 @ 
% 0.36/0.60               (k1_zfmisc_1 @ 
% 0.36/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))))
% 0.36/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.60          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 0.36/0.60          | (r1_tmap_1 @ X19 @ X24 @ X25 @ X23)
% 0.36/0.60          | ~ (r1_tmap_1 @ X20 @ X24 @ (k2_tmap_1 @ X19 @ X24 @ X25 @ X20) @ 
% 0.36/0.60               X23)
% 0.36/0.60          | ~ (m1_connsp_2 @ X22 @ X19 @ X23)
% 0.36/0.60          | ~ (r1_tarski @ X22 @ (u1_struct_0 @ X20))
% 0.36/0.60          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 0.36/0.60          | ~ (m1_pre_topc @ X20 @ X19)
% 0.36/0.60          | (v2_struct_0 @ X20)
% 0.36/0.60          | ~ (l1_pre_topc @ X19)
% 0.36/0.60          | ~ (v2_pre_topc @ X19)
% 0.36/0.60          | (v2_struct_0 @ X19))),
% 0.36/0.60      inference('simplify', [status(thm)], ['113'])).
% 0.36/0.60  thf('115', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | (v2_struct_0 @ X0)
% 0.36/0.60          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.36/0.60          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.60          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.36/0.60          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.36/0.60          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60               (u1_struct_0 @ sk_A))
% 0.36/0.60          | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.60          | (v2_struct_0 @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['112', '114'])).
% 0.36/0.60  thf('116', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('117', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('118', plain,
% 0.36/0.60      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('119', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('122', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | (v2_struct_0 @ X0)
% 0.36/0.60          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.36/0.60          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.60          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.36/0.60          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.36/0.60          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.36/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60          | (v2_struct_0 @ sk_A))),
% 0.36/0.60      inference('demod', [status(thm)],
% 0.36/0.60                ['115', '116', '117', '118', '119', '120', '121'])).
% 0.36/0.60  thf('123', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((v2_struct_0 @ sk_A)
% 0.36/0.60           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))
% 0.36/0.60           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.36/0.60           | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.36/0.60           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.36/0.60           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.36/0.60           | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.36/0.60           | (v2_struct_0 @ sk_D_1)
% 0.36/0.60           | (v2_struct_0 @ sk_B)))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['111', '122'])).
% 0.36/0.60  thf('124', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('125', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('126', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('127', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((v2_struct_0 @ sk_A)
% 0.36/0.60           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.60           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.36/0.60           | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.36/0.60           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.36/0.60           | (v2_struct_0 @ sk_D_1)
% 0.36/0.60           | (v2_struct_0 @ sk_B)))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.36/0.60      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.36/0.60  thf('128', plain,
% 0.36/0.60      ((((v2_struct_0 @ sk_B)
% 0.36/0.60         | (v2_struct_0 @ sk_D_1)
% 0.36/0.60         | ~ (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60              (u1_struct_0 @ sk_D_1))
% 0.36/0.60         | ~ (m1_connsp_2 @ 
% 0.36/0.60              (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ sk_B @ sk_G)
% 0.36/0.60         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.36/0.60         | (v2_struct_0 @ sk_A)))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['110', '127'])).
% 0.36/0.60  thf('129', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('130', plain,
% 0.36/0.60      ((m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)),
% 0.36/0.60      inference('clc', [status(thm)], ['86', '87'])).
% 0.36/0.60  thf('131', plain,
% 0.36/0.60      ((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.36/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('clc', [status(thm)], ['98', '99'])).
% 0.36/0.60  thf('132', plain,
% 0.36/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.36/0.60          | (r1_tarski @ (sk_D @ X18 @ X16 @ X17) @ X18)
% 0.36/0.60          | ~ (m1_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.60          | ~ (l1_pre_topc @ X17)
% 0.36/0.60          | ~ (v2_pre_topc @ X17)
% 0.36/0.60          | (v2_struct_0 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.36/0.60  thf('133', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.36/0.60          | (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.36/0.60             (sk_D @ sk_E @ sk_G @ sk_B))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['131', '132'])).
% 0.36/0.60  thf('134', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('135', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('136', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.36/0.60          | (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.36/0.60             (sk_D @ sk_E @ sk_G @ sk_B))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.36/0.60  thf('137', plain,
% 0.36/0.60      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.36/0.60        | (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60           (sk_D @ sk_E @ sk_G @ sk_B))
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['130', '136'])).
% 0.36/0.60  thf('138', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('139', plain,
% 0.36/0.60      (((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60         (sk_D @ sk_E @ sk_G @ sk_B))
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['137', '138'])).
% 0.36/0.60  thf('140', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('141', plain,
% 0.36/0.60      ((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60        (sk_D @ sk_E @ sk_G @ sk_B))),
% 0.36/0.60      inference('clc', [status(thm)], ['139', '140'])).
% 0.36/0.60  thf('142', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.60          | (r2_hidden @ X0 @ X2)
% 0.36/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('143', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B))
% 0.36/0.60          | ~ (r2_hidden @ X0 @ 
% 0.36/0.60               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['141', '142'])).
% 0.36/0.60  thf('144', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ X0)
% 0.36/0.60          | (r2_hidden @ 
% 0.36/0.60             (sk_C @ X0 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B)) @ 
% 0.36/0.60             (sk_D @ sk_E @ sk_G @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['129', '143'])).
% 0.36/0.60  thf('145', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('146', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.36/0.60      inference('clc', [status(thm)], ['60', '61'])).
% 0.36/0.60  thf('147', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('148', plain,
% 0.36/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.36/0.60          | (r1_tarski @ (sk_D @ X18 @ X16 @ X17) @ X18)
% 0.36/0.60          | ~ (m1_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.60          | ~ (l1_pre_topc @ X17)
% 0.36/0.60          | ~ (v2_pre_topc @ X17)
% 0.36/0.60          | (v2_struct_0 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.36/0.60  thf('149', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.36/0.60          | (r1_tarski @ (sk_D @ sk_E @ X0 @ sk_B) @ sk_E)
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['147', '148'])).
% 0.36/0.60  thf('150', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('151', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('152', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.36/0.60          | (r1_tarski @ (sk_D @ sk_E @ X0 @ sk_B) @ sk_E)
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.36/0.60  thf('153', plain,
% 0.36/0.60      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.36/0.60        | (r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_E)
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['146', '152'])).
% 0.36/0.60  thf('154', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('155', plain,
% 0.36/0.60      (((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_E) | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['153', '154'])).
% 0.36/0.60  thf('156', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('157', plain, ((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_E)),
% 0.36/0.60      inference('clc', [status(thm)], ['155', '156'])).
% 0.36/0.60  thf('158', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.60          | (r2_hidden @ X0 @ X2)
% 0.36/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('159', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ X0 @ sk_E)
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['157', '158'])).
% 0.36/0.60  thf('160', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0)
% 0.36/0.60          | (r2_hidden @ (sk_C @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B)) @ sk_E))),
% 0.36/0.60      inference('sup-', [status(thm)], ['145', '159'])).
% 0.36/0.60  thf('161', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('162', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.60          | (r2_hidden @ X0 @ X2)
% 0.36/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('163', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.36/0.60      inference('sup-', [status(thm)], ['161', '162'])).
% 0.36/0.60  thf('164', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0)
% 0.36/0.60          | (r2_hidden @ (sk_C @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B)) @ 
% 0.36/0.60             (u1_struct_0 @ sk_D_1)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['160', '163'])).
% 0.36/0.60  thf('165', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('166', plain,
% 0.36/0.60      (((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.36/0.60        | (r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ (u1_struct_0 @ sk_D_1)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['164', '165'])).
% 0.36/0.60  thf('167', plain,
% 0.36/0.60      ((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ (u1_struct_0 @ sk_D_1))),
% 0.36/0.60      inference('simplify', [status(thm)], ['166'])).
% 0.36/0.60  thf('168', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.60          | (r2_hidden @ X0 @ X2)
% 0.36/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('169', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['167', '168'])).
% 0.36/0.60  thf('170', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ X0)
% 0.36/0.60          | (r2_hidden @ 
% 0.36/0.60             (sk_C @ X0 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B)) @ 
% 0.36/0.60             (u1_struct_0 @ sk_D_1)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['144', '169'])).
% 0.36/0.60  thf('171', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('172', plain,
% 0.36/0.60      (((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60         (u1_struct_0 @ sk_D_1))
% 0.36/0.60        | (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60           (u1_struct_0 @ sk_D_1)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['170', '171'])).
% 0.36/0.60  thf('173', plain,
% 0.36/0.60      ((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60        (u1_struct_0 @ sk_D_1))),
% 0.36/0.60      inference('simplify', [status(thm)], ['172'])).
% 0.36/0.60  thf('174', plain,
% 0.36/0.60      ((m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)),
% 0.36/0.60      inference('clc', [status(thm)], ['86', '87'])).
% 0.36/0.60  thf('175', plain,
% 0.36/0.60      ((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.36/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('clc', [status(thm)], ['98', '99'])).
% 0.36/0.60  thf('176', plain,
% 0.36/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.36/0.60          | (m1_connsp_2 @ (sk_D @ X18 @ X16 @ X17) @ X17 @ X16)
% 0.36/0.60          | ~ (m1_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.60          | ~ (l1_pre_topc @ X17)
% 0.36/0.60          | ~ (v2_pre_topc @ X17)
% 0.36/0.60          | (v2_struct_0 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.36/0.60  thf('177', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.36/0.60          | (m1_connsp_2 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.36/0.60             sk_B @ X0)
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['175', '176'])).
% 0.36/0.60  thf('178', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('179', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('180', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((v2_struct_0 @ sk_B)
% 0.36/0.60          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.36/0.60          | (m1_connsp_2 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.36/0.60             sk_B @ X0)
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['177', '178', '179'])).
% 0.36/0.60  thf('181', plain,
% 0.36/0.60      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.36/0.60        | (m1_connsp_2 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60           sk_B @ sk_G)
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['174', '180'])).
% 0.36/0.60  thf('182', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('183', plain,
% 0.36/0.60      (((m1_connsp_2 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60         sk_B @ sk_G)
% 0.36/0.60        | (v2_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['181', '182'])).
% 0.36/0.60  thf('184', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('185', plain,
% 0.36/0.60      ((m1_connsp_2 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.36/0.60        sk_B @ sk_G)),
% 0.36/0.60      inference('clc', [status(thm)], ['183', '184'])).
% 0.36/0.60  thf('186', plain,
% 0.36/0.60      ((((v2_struct_0 @ sk_B)
% 0.36/0.60         | (v2_struct_0 @ sk_D_1)
% 0.36/0.60         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.36/0.60         | (v2_struct_0 @ sk_A)))
% 0.36/0.60         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.36/0.60      inference('demod', [status(thm)], ['128', '173', '185'])).
% 0.36/0.60  thf('187', plain,
% 0.36/0.60      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.36/0.60         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.36/0.60      inference('split', [status(esa)], ['2'])).
% 0.36/0.60  thf('188', plain,
% 0.36/0.60      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.36/0.60         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)) & 
% 0.36/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['186', '187'])).
% 0.36/0.60  thf('189', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('190', plain,
% 0.36/0.60      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.36/0.60         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)) & 
% 0.36/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.36/0.60      inference('clc', [status(thm)], ['188', '189'])).
% 0.36/0.60  thf('191', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('192', plain,
% 0.36/0.60      (((v2_struct_0 @ sk_D_1))
% 0.36/0.60         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)) & 
% 0.36/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.36/0.60      inference('clc', [status(thm)], ['190', '191'])).
% 0.36/0.60  thf('193', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('194', plain,
% 0.36/0.60      (~
% 0.36/0.60       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.36/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) | 
% 0.36/0.60       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.36/0.60      inference('sup-', [status(thm)], ['192', '193'])).
% 0.36/0.60  thf('195', plain, ($false),
% 0.36/0.60      inference('sat_resolution*', [status(thm)],
% 0.36/0.60                ['3', '12', '75', '76', '194'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
