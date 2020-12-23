%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R697vmXOOd

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:23 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 673 expanded)
%              Number of leaves         :   41 ( 207 expanded)
%              Depth                    :   30
%              Number of atoms          : 2212 (25926 expanded)
%              Number of equality atoms :   27 ( 361 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t87_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ B )
                          & ( m1_pre_topc @ C @ B )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

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
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                       => ( ( ( v1_tsep_1 @ C @ B )
                            & ( m1_pre_topc @ C @ B )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t19_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
               => ( ( v1_tsep_1 @ B @ C )
                  & ( m1_pre_topc @ B @ C ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_tsep_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X29 ) )
      | ( v1_tsep_1 @ X27 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v1_tsep_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X25 )
      | ( ( k3_tmap_1 @ X24 @ X22 @ X25 @ X23 @ X26 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) @ X26 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( ( k2_tmap_1 @ X20 @ X18 @ X21 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) @ X21 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('53',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('58',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','56','57','58','59','60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['31','73'])).

thf('75',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['28'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
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
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ( r1_tmap_1 @ X33 @ X35 @ ( k2_tmap_1 @ X32 @ X35 @ X36 @ X33 ) @ X34 )
      | ( X37 != X34 )
      | ~ ( r1_tmap_1 @ X32 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('83',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_tmap_1 @ X32 @ X35 @ X36 @ X34 )
      | ( r1_tmap_1 @ X33 @ X35 @ ( k2_tmap_1 @ X32 @ X35 @ X36 @ X33 ) @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('86',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('87',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['80','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['79','94'])).

thf('96',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('99',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['75'])).

thf('100',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['28'])).

thf('111',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['76','109','110'])).

thf('112',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['74','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_tmap_1,axiom,(
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
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

thf('114',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( v1_tsep_1 @ X39 @ X38 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r1_tmap_1 @ X39 @ X41 @ ( k2_tmap_1 @ X38 @ X41 @ X42 @ X39 ) @ X40 )
      | ( r1_tmap_1 @ X38 @ X41 @ X42 @ X43 )
      | ( X43 != X40 )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('115',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X38 ) )
      | ( r1_tmap_1 @ X38 @ X41 @ X42 @ X40 )
      | ~ ( r1_tmap_1 @ X39 @ X41 @ ( k2_tmap_1 @ X38 @ X41 @ X42 @ X39 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( v1_tsep_1 @ X39 @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('118',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('119',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['112','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('127',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['75'])).

thf('132',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['76','109'])).

thf('133',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('135',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('138',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('139',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['136','139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['0','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R697vmXOOd
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 167 iterations in 0.086s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.36/0.54  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.54  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.36/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(t87_tmap_1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54             ( l1_pre_topc @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.54                   ( ![E:$i]:
% 0.36/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.54                         ( v1_funct_2 @
% 0.36/0.54                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.54                         ( m1_subset_1 @
% 0.36/0.54                           E @ 
% 0.36/0.54                           ( k1_zfmisc_1 @
% 0.36/0.54                             ( k2_zfmisc_1 @
% 0.36/0.54                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.54                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.36/0.54                           ( m1_pre_topc @ C @ D ) ) =>
% 0.36/0.54                         ( ![F:$i]:
% 0.36/0.54                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.54                             ( ![G:$i]:
% 0.36/0.54                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.54                                 ( ( ( F ) = ( G ) ) =>
% 0.36/0.54                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.36/0.54                                     ( r1_tmap_1 @
% 0.36/0.54                                       C @ A @ 
% 0.36/0.54                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.54            ( l1_pre_topc @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54                ( l1_pre_topc @ B ) ) =>
% 0.36/0.54              ( ![C:$i]:
% 0.36/0.54                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.36/0.54                  ( ![D:$i]:
% 0.36/0.54                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.54                      ( ![E:$i]:
% 0.36/0.54                        ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.54                            ( v1_funct_2 @
% 0.36/0.54                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.54                            ( m1_subset_1 @
% 0.36/0.54                              E @ 
% 0.36/0.54                              ( k1_zfmisc_1 @
% 0.36/0.54                                ( k2_zfmisc_1 @
% 0.36/0.54                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.54                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.36/0.54                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.36/0.54                            ( ![F:$i]:
% 0.36/0.54                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.54                                ( ![G:$i]:
% 0.36/0.54                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.54                                    ( ( ( F ) = ( G ) ) =>
% 0.36/0.54                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.36/0.54                                        ( r1_tmap_1 @
% 0.36/0.54                                          C @ A @ 
% 0.36/0.54                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.36/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d3_tarski, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X1 : $i, X3 : $i]:
% 0.36/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.54  thf('3', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t1_tsep_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.54           ( m1_subset_1 @
% 0.36/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X30 : $i, X31 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X30 @ X31)
% 0.36/0.54          | (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.36/0.54          | ~ (l1_pre_topc @ X31))),
% 0.36/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_D)
% 0.36/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(dt_m1_pre_topc, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X12 @ X13)
% 0.36/0.54          | (l1_pre_topc @ X12)
% 0.36/0.54          | ~ (l1_pre_topc @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.54  thf('8', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.36/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.54  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('10', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.36/0.54      inference('demod', [status(thm)], ['5', '10'])).
% 0.36/0.54  thf(t4_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.36/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X6 @ X7)
% 0.36/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.36/0.54          | (m1_subset_1 @ X6 @ X8))),
% 0.36/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.36/0.54          | (m1_subset_1 @ (sk_C @ X0 @ (u1_struct_0 @ sk_C_1)) @ 
% 0.36/0.54             (u1_struct_0 @ sk_D)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['2', '13'])).
% 0.36/0.54  thf(t2_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i]:
% 0.36/0.54         ((r2_hidden @ X4 @ X5)
% 0.36/0.54          | (v1_xboole_0 @ X5)
% 0.36/0.54          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.36/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.36/0.54          | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_C_1)) @ 
% 0.36/0.54             (u1_struct_0 @ sk_D)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X1 : $i, X3 : $i]:
% 0.36/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.36/0.54        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.36/0.54        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.36/0.54  thf(t19_tsep_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.54               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.54                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.54         (~ (v1_tsep_1 @ X27 @ X28)
% 0.36/0.54          | ~ (m1_pre_topc @ X27 @ X28)
% 0.36/0.54          | ~ (r1_tarski @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X29))
% 0.36/0.54          | (v1_tsep_1 @ X27 @ X29)
% 0.36/0.54          | ~ (m1_pre_topc @ X29 @ X28)
% 0.36/0.54          | (v2_struct_0 @ X29)
% 0.36/0.54          | ~ (l1_pre_topc @ X28)
% 0.36/0.54          | ~ (v2_pre_topc @ X28)
% 0.36/0.54          | (v2_struct_0 @ X28))),
% 0.36/0.54      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.36/0.54          | (v2_struct_0 @ X0)
% 0.36/0.54          | ~ (v2_pre_topc @ X0)
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_D)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.54          | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.36/0.54          | ~ (v1_tsep_1 @ sk_C_1 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      ((~ (v1_tsep_1 @ sk_C_1 @ sk_B)
% 0.36/0.54        | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.36/0.54        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.54        | (v2_struct_0 @ sk_D)
% 0.36/0.54        | ~ (l1_pre_topc @ sk_B)
% 0.36/0.54        | ~ (v2_pre_topc @ sk_B)
% 0.36/0.54        | (v2_struct_0 @ sk_B)
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '21'])).
% 0.36/0.54  thf('23', plain, ((v1_tsep_1 @ sk_C_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('24', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('26', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.54        | (v2_struct_0 @ sk_D)
% 0.36/0.54        | (v2_struct_0 @ sk_B)
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.36/0.54      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.36/0.54        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('split', [status(esa)], ['28'])).
% 0.36/0.54  thf('30', plain, (((sk_F) = (sk_G))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.54  thf('32', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('33', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d5_tmap_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54             ( l1_pre_topc @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_pre_topc @ C @ A ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( m1_pre_topc @ D @ A ) =>
% 0.36/0.54                   ( ![E:$i]:
% 0.36/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.54                         ( v1_funct_2 @
% 0.36/0.54                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                         ( m1_subset_1 @
% 0.36/0.54                           E @ 
% 0.36/0.54                           ( k1_zfmisc_1 @
% 0.36/0.54                             ( k2_zfmisc_1 @
% 0.36/0.54                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54                       ( ( m1_pre_topc @ D @ C ) =>
% 0.36/0.54                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.36/0.54                           ( k2_partfun1 @
% 0.36/0.54                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.36/0.54                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X22)
% 0.36/0.54          | ~ (v2_pre_topc @ X22)
% 0.36/0.54          | ~ (l1_pre_topc @ X22)
% 0.36/0.54          | ~ (m1_pre_topc @ X23 @ X24)
% 0.36/0.54          | ~ (m1_pre_topc @ X23 @ X25)
% 0.36/0.54          | ((k3_tmap_1 @ X24 @ X22 @ X25 @ X23 @ X26)
% 0.36/0.54              = (k2_partfun1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22) @ 
% 0.36/0.54                 X26 @ (u1_struct_0 @ X23)))
% 0.36/0.54          | ~ (m1_subset_1 @ X26 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))))
% 0.36/0.54          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))
% 0.36/0.54          | ~ (v1_funct_1 @ X26)
% 0.36/0.54          | ~ (m1_pre_topc @ X25 @ X24)
% 0.36/0.54          | ~ (l1_pre_topc @ X24)
% 0.36/0.54          | ~ (v2_pre_topc @ X24)
% 0.36/0.54          | (v2_struct_0 @ X24))),
% 0.36/0.54      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X0)
% 0.36/0.54          | ~ (v2_pre_topc @ X0)
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.54          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.36/0.54          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.36/0.54              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                 sk_E @ (u1_struct_0 @ X1)))
% 0.36/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.36/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.54  thf('37', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X0)
% 0.36/0.54          | ~ (v2_pre_topc @ X0)
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.54          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.36/0.54              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                 sk_E @ (u1_struct_0 @ X1)))
% 0.36/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.36/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.54          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.36/0.54              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                 sk_E @ (u1_struct_0 @ X0)))
% 0.36/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.54          | (v2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['33', '41'])).
% 0.36/0.54  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('44', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.54          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.36/0.54              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                 sk_E @ (u1_struct_0 @ X0)))
% 0.36/0.54          | (v2_struct_0 @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_B)
% 0.36/0.54        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.36/0.54            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.36/0.54        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['32', '45'])).
% 0.36/0.54  thf('47', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d4_tmap_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54             ( l1_pre_topc @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                 ( m1_subset_1 @
% 0.36/0.54                   C @ 
% 0.36/0.54                   ( k1_zfmisc_1 @
% 0.36/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( m1_pre_topc @ D @ A ) =>
% 0.36/0.54                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.36/0.54                     ( k2_partfun1 @
% 0.36/0.54                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.36/0.54                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X18)
% 0.36/0.54          | ~ (v2_pre_topc @ X18)
% 0.36/0.54          | ~ (l1_pre_topc @ X18)
% 0.36/0.54          | ~ (m1_pre_topc @ X19 @ X20)
% 0.36/0.54          | ((k2_tmap_1 @ X20 @ X18 @ X21 @ X19)
% 0.36/0.54              = (k2_partfun1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18) @ 
% 0.36/0.54                 X21 @ (u1_struct_0 @ X19)))
% 0.36/0.54          | ~ (m1_subset_1 @ X21 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.36/0.54          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.36/0.54          | ~ (v1_funct_1 @ X21)
% 0.36/0.54          | ~ (l1_pre_topc @ X20)
% 0.36/0.54          | ~ (v2_pre_topc @ X20)
% 0.36/0.54          | (v2_struct_0 @ X20))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_D)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_D)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_D)
% 0.36/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.54          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.36/0.54          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.36/0.54              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                 sk_E @ (u1_struct_0 @ X0)))
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.54  thf('51', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc1_pre_topc, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      (![X9 : $i, X10 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X9 @ X10)
% 0.36/0.54          | (v2_pre_topc @ X9)
% 0.36/0.54          | ~ (l1_pre_topc @ X10)
% 0.36/0.54          | ~ (v2_pre_topc @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.36/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.54  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('56', plain, ((v2_pre_topc @ sk_D)),
% 0.36/0.54      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.36/0.54  thf('57', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf('58', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('59', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_D)
% 0.36/0.54          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.36/0.54              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                 sk_E @ (u1_struct_0 @ X0)))
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)],
% 0.36/0.54                ['50', '56', '57', '58', '59', '60', '61'])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.36/0.54            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.36/0.54        | (v2_struct_0 @ sk_D))),
% 0.36/0.54      inference('sup-', [status(thm)], ['47', '62'])).
% 0.36/0.54  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_D)
% 0.36/0.54        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.36/0.54            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.36/0.54      inference('clc', [status(thm)], ['63', '64'])).
% 0.36/0.54  thf('66', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('67', plain,
% 0.36/0.54      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.36/0.54         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.36/0.54            (u1_struct_0 @ sk_C_1)))),
% 0.36/0.54      inference('clc', [status(thm)], ['65', '66'])).
% 0.36/0.54  thf('68', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('69', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_B)
% 0.36/0.54        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.36/0.54            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['46', '67', '68'])).
% 0.36/0.54  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('71', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.36/0.54            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)))),
% 0.36/0.54      inference('clc', [status(thm)], ['69', '70'])).
% 0.36/0.54  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('73', plain,
% 0.36/0.54      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.36/0.54         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))),
% 0.36/0.54      inference('clc', [status(thm)], ['71', '72'])).
% 0.36/0.54  thf('74', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54         (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('demod', [status(thm)], ['31', '73'])).
% 0.36/0.54  thf('75', plain,
% 0.36/0.54      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.36/0.54        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('76', plain,
% 0.36/0.54      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.36/0.54       ~
% 0.36/0.54       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.36/0.54      inference('split', [status(esa)], ['75'])).
% 0.36/0.54  thf('77', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('78', plain, (((sk_F) = (sk_G))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('79', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['77', '78'])).
% 0.36/0.54  thf('80', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.54      inference('split', [status(esa)], ['28'])).
% 0.36/0.54  thf('81', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t64_tmap_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54             ( l1_pre_topc @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.54                 ( m1_subset_1 @
% 0.36/0.54                   C @ 
% 0.36/0.54                   ( k1_zfmisc_1 @
% 0.36/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.54                   ( ![E:$i]:
% 0.36/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.54                       ( ![F:$i]:
% 0.36/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.54                           ( ( ( ( E ) = ( F ) ) & 
% 0.36/0.54                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.36/0.54                             ( r1_tmap_1 @
% 0.36/0.54                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('82', plain,
% 0.36/0.54      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X32)
% 0.36/0.54          | ~ (v2_pre_topc @ X32)
% 0.36/0.54          | ~ (l1_pre_topc @ X32)
% 0.36/0.54          | (v2_struct_0 @ X33)
% 0.36/0.54          | ~ (m1_pre_topc @ X33 @ X32)
% 0.36/0.54          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.36/0.54          | (r1_tmap_1 @ X33 @ X35 @ (k2_tmap_1 @ X32 @ X35 @ X36 @ X33) @ X34)
% 0.36/0.54          | ((X37) != (X34))
% 0.36/0.54          | ~ (r1_tmap_1 @ X32 @ X35 @ X36 @ X37)
% 0.36/0.54          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X32))
% 0.36/0.54          | ~ (m1_subset_1 @ X36 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))))
% 0.36/0.54          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))
% 0.36/0.54          | ~ (v1_funct_1 @ X36)
% 0.36/0.54          | ~ (l1_pre_topc @ X35)
% 0.36/0.54          | ~ (v2_pre_topc @ X35)
% 0.36/0.54          | (v2_struct_0 @ X35))),
% 0.36/0.54      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.36/0.54  thf('83', plain,
% 0.36/0.54      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X35)
% 0.36/0.54          | ~ (v2_pre_topc @ X35)
% 0.36/0.54          | ~ (l1_pre_topc @ X35)
% 0.36/0.54          | ~ (v1_funct_1 @ X36)
% 0.36/0.54          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))
% 0.36/0.54          | ~ (m1_subset_1 @ X36 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))))
% 0.36/0.54          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 0.36/0.54          | ~ (r1_tmap_1 @ X32 @ X35 @ X36 @ X34)
% 0.36/0.54          | (r1_tmap_1 @ X33 @ X35 @ (k2_tmap_1 @ X32 @ X35 @ X36 @ X33) @ X34)
% 0.36/0.54          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.36/0.54          | ~ (m1_pre_topc @ X33 @ X32)
% 0.36/0.54          | (v2_struct_0 @ X33)
% 0.36/0.54          | ~ (l1_pre_topc @ X32)
% 0.36/0.54          | ~ (v2_pre_topc @ X32)
% 0.36/0.54          | (v2_struct_0 @ X32))),
% 0.36/0.54      inference('simplify', [status(thm)], ['82'])).
% 0.36/0.54  thf('84', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_D)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_D)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_D)
% 0.36/0.54          | (v2_struct_0 @ X0)
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.36/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.36/0.54          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.36/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['81', '83'])).
% 0.36/0.54  thf('85', plain, ((v2_pre_topc @ sk_D)),
% 0.36/0.54      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.36/0.54  thf('86', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf('87', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('91', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_D)
% 0.36/0.54          | (v2_struct_0 @ X0)
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.36/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)],
% 0.36/0.54                ['84', '85', '86', '87', '88', '89', '90'])).
% 0.36/0.54  thf('92', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          ((v2_struct_0 @ sk_A)
% 0.36/0.54           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.36/0.54           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.36/0.54              sk_F)
% 0.36/0.54           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.36/0.54           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.54           | (v2_struct_0 @ X0)
% 0.36/0.54           | (v2_struct_0 @ sk_D)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['80', '91'])).
% 0.36/0.54  thf('93', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('94', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          ((v2_struct_0 @ sk_A)
% 0.36/0.54           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.36/0.54              sk_F)
% 0.36/0.54           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.36/0.54           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.54           | (v2_struct_0 @ X0)
% 0.36/0.54           | (v2_struct_0 @ sk_D)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['92', '93'])).
% 0.36/0.54  thf('95', plain,
% 0.36/0.54      ((((v2_struct_0 @ sk_D)
% 0.36/0.54         | (v2_struct_0 @ sk_C_1)
% 0.36/0.54         | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.36/0.54         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)
% 0.36/0.54         | (v2_struct_0 @ sk_A)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['79', '94'])).
% 0.36/0.54  thf('96', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('97', plain,
% 0.36/0.54      ((((v2_struct_0 @ sk_D)
% 0.36/0.54         | (v2_struct_0 @ sk_C_1)
% 0.36/0.54         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)
% 0.36/0.54         | (v2_struct_0 @ sk_A)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['95', '96'])).
% 0.36/0.54  thf('98', plain,
% 0.36/0.54      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.36/0.54         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))),
% 0.36/0.54      inference('clc', [status(thm)], ['71', '72'])).
% 0.36/0.54  thf('99', plain,
% 0.36/0.54      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('split', [status(esa)], ['75'])).
% 0.36/0.54  thf('100', plain, (((sk_F) = (sk_G))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('101', plain,
% 0.36/0.54      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('demod', [status(thm)], ['99', '100'])).
% 0.36/0.54  thf('102', plain,
% 0.36/0.54      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54           (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['98', '101'])).
% 0.36/0.54  thf('103', plain,
% 0.36/0.54      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D)))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.36/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['97', '102'])).
% 0.36/0.54  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('105', plain,
% 0.36/0.54      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1)))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.36/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.54      inference('clc', [status(thm)], ['103', '104'])).
% 0.36/0.54  thf('106', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('107', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_C_1))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.36/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.54      inference('clc', [status(thm)], ['105', '106'])).
% 0.36/0.54  thf('108', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('109', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.36/0.54       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.54      inference('sup-', [status(thm)], ['107', '108'])).
% 0.36/0.54  thf('110', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.36/0.54       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.54      inference('split', [status(esa)], ['28'])).
% 0.36/0.54  thf('111', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['76', '109', '110'])).
% 0.36/0.54  thf('112', plain,
% 0.36/0.54      ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.54        (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['74', '111'])).
% 0.36/0.54  thf('113', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t67_tmap_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54             ( l1_pre_topc @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.54                 ( m1_subset_1 @
% 0.36/0.54                   C @ 
% 0.36/0.54                   ( k1_zfmisc_1 @
% 0.36/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.36/0.54                     ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.54                   ( ![E:$i]:
% 0.36/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.54                       ( ![F:$i]:
% 0.36/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.55                           ( ( ( E ) = ( F ) ) =>
% 0.36/0.55                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.36/0.55                               ( r1_tmap_1 @
% 0.36/0.55                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('114', plain,
% 0.36/0.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X38)
% 0.36/0.55          | ~ (v2_pre_topc @ X38)
% 0.36/0.55          | ~ (l1_pre_topc @ X38)
% 0.36/0.55          | (v2_struct_0 @ X39)
% 0.36/0.55          | ~ (v1_tsep_1 @ X39 @ X38)
% 0.36/0.55          | ~ (m1_pre_topc @ X39 @ X38)
% 0.36/0.55          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 0.36/0.55          | ~ (r1_tmap_1 @ X39 @ X41 @ (k2_tmap_1 @ X38 @ X41 @ X42 @ X39) @ 
% 0.36/0.55               X40)
% 0.36/0.55          | (r1_tmap_1 @ X38 @ X41 @ X42 @ X43)
% 0.36/0.55          | ((X43) != (X40))
% 0.36/0.55          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X38))
% 0.36/0.55          | ~ (m1_subset_1 @ X42 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X41))))
% 0.36/0.55          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X41))
% 0.36/0.55          | ~ (v1_funct_1 @ X42)
% 0.36/0.55          | ~ (l1_pre_topc @ X41)
% 0.36/0.55          | ~ (v2_pre_topc @ X41)
% 0.36/0.55          | (v2_struct_0 @ X41))),
% 0.36/0.55      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.36/0.55  thf('115', plain,
% 0.36/0.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X41)
% 0.36/0.55          | ~ (v2_pre_topc @ X41)
% 0.36/0.55          | ~ (l1_pre_topc @ X41)
% 0.36/0.55          | ~ (v1_funct_1 @ X42)
% 0.36/0.55          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X41))
% 0.36/0.55          | ~ (m1_subset_1 @ X42 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X41))))
% 0.36/0.55          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X38))
% 0.36/0.55          | (r1_tmap_1 @ X38 @ X41 @ X42 @ X40)
% 0.36/0.55          | ~ (r1_tmap_1 @ X39 @ X41 @ (k2_tmap_1 @ X38 @ X41 @ X42 @ X39) @ 
% 0.36/0.55               X40)
% 0.36/0.55          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 0.36/0.55          | ~ (m1_pre_topc @ X39 @ X38)
% 0.36/0.55          | ~ (v1_tsep_1 @ X39 @ X38)
% 0.36/0.55          | (v2_struct_0 @ X39)
% 0.36/0.55          | ~ (l1_pre_topc @ X38)
% 0.36/0.55          | ~ (v2_pre_topc @ X38)
% 0.36/0.55          | (v2_struct_0 @ X38))),
% 0.36/0.55      inference('simplify', [status(thm)], ['114'])).
% 0.36/0.55  thf('116', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_D)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.36/0.55               X1)
% 0.36/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.36/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['113', '115'])).
% 0.36/0.55  thf('117', plain, ((v2_pre_topc @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.36/0.55  thf('118', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('119', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('120', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('123', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_D)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.36/0.55               X1)
% 0.36/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)],
% 0.36/0.55                ['116', '117', '118', '119', '120', '121', '122'])).
% 0.36/0.55  thf('124', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.36/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.36/0.55        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.36/0.55        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.36/0.55        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1)
% 0.36/0.55        | (v2_struct_0 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['112', '123'])).
% 0.36/0.55  thf('125', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('126', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['77', '78'])).
% 0.36/0.55  thf('127', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('128', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.36/0.55        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1)
% 0.36/0.55        | (v2_struct_0 @ sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.36/0.55  thf('129', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1)
% 0.36/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.36/0.55        | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['27', '128'])).
% 0.36/0.55  thf('130', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['129'])).
% 0.36/0.55  thf('131', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.36/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.55      inference('split', [status(esa)], ['75'])).
% 0.36/0.55  thf('132', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['76', '109'])).
% 0.36/0.55  thf('133', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['131', '132'])).
% 0.36/0.55  thf('134', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['130', '133'])).
% 0.36/0.55  thf(fc2_struct_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('135', plain,
% 0.36/0.55      (![X14 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.36/0.55          | ~ (l1_struct_0 @ X14)
% 0.36/0.55          | (v2_struct_0 @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.55  thf('136', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | ~ (l1_struct_0 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['134', '135'])).
% 0.36/0.55  thf('137', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf(dt_l1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.55  thf('138', plain,
% 0.36/0.55      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('139', plain, ((l1_struct_0 @ sk_D)),
% 0.36/0.55      inference('sup-', [status(thm)], ['137', '138'])).
% 0.36/0.55  thf('140', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['136', '139'])).
% 0.36/0.55  thf('141', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('simplify', [status(thm)], ['140'])).
% 0.36/0.55  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('143', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['141', '142'])).
% 0.36/0.55  thf('144', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('145', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 0.36/0.55      inference('clc', [status(thm)], ['143', '144'])).
% 0.36/0.55  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('147', plain, ((v2_struct_0 @ sk_D)),
% 0.36/0.55      inference('clc', [status(thm)], ['145', '146'])).
% 0.36/0.55  thf('148', plain, ($false), inference('demod', [status(thm)], ['0', '147'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
