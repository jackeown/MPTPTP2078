%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTa8LCSwmC

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 319 expanded)
%              Number of leaves         :   37 ( 104 expanded)
%              Depth                    :   26
%              Number of atoms          : 1551 (10157 expanded)
%              Number of equality atoms :   13 ( 149 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t67_tmap_1,conjecture,(
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
                      & ( v1_tsep_1 @ D @ B )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ( ( E = F )
                             => ( ( r1_tmap_1 @ B @ A @ C @ E )
                              <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('18',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['11'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( r1_tmap_1 @ X23 @ X25 @ ( k2_tmap_1 @ X22 @ X25 @ X26 @ X23 ) @ X24 )
      | ( X27 != X24 )
      | ~ ( r1_tmap_1 @ X22 @ X25 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_tmap_1 @ X22 @ X25 @ X26 @ X24 )
      | ( r1_tmap_1 @ X23 @ X25 @ ( k2_tmap_1 @ X22 @ X25 @ X26 @ X23 ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
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
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26','27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['15'])).

thf('37',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['11'])).

thf('47',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['16','45','46'])).

thf('48',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['14','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t66_tmap_1,axiom,(
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

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( v3_pre_topc @ X31 @ X28 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( X30 != X32 )
      | ~ ( r1_tmap_1 @ X29 @ X33 @ ( k2_tmap_1 @ X28 @ X33 @ X34 @ X29 ) @ X32 )
      | ( r1_tmap_1 @ X28 @ X33 @ X34 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('51',plain,(
    ! [X28: $i,X29: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X28 @ X33 @ X34 @ X32 )
      | ~ ( r1_tmap_1 @ X29 @ X33 @ ( k2_tmap_1 @ X28 @ X33 @ X34 @ X29 ) @ X32 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X32 @ X31 )
      | ~ ( v3_pre_topc @ X31 @ X28 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X2 @ sk_B )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X2 @ sk_B )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','64'])).

thf('66',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_tsep_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('75',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('77',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('78',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','74','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','80'])).

thf('82',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['15'])).

thf('83',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['16','45'])).

thf('84',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('86',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('93',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('94',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['87','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['0','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTa8LCSwmC
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:32:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 88 iterations in 0.053s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(t67_tmap_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.53                     ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                           ( ( ( E ) = ( F ) ) =>
% 0.21/0.53                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.53                               ( r1_tmap_1 @
% 0.21/0.53                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53                ( l1_pre_topc @ B ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                    ( v1_funct_2 @
% 0.21/0.53                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                    ( m1_subset_1 @
% 0.21/0.53                      C @ 
% 0.21/0.53                      ( k1_zfmisc_1 @
% 0.21/0.53                        ( k2_zfmisc_1 @
% 0.21/0.53                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53                  ( ![D:$i]:
% 0.21/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.53                        ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                      ( ![E:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                          ( ![F:$i]:
% 0.21/0.53                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                              ( ( ( E ) = ( F ) ) =>
% 0.21/0.53                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.53                                  ( r1_tmap_1 @
% 0.21/0.53                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain, (((sk_E) = (sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(t2_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         ((r2_hidden @ X2 @ X3)
% 0.21/0.53          | (v1_xboole_0 @ X3)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.53        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t1_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( m1_subset_1 @
% 0.21/0.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.53          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.53          | ~ (l1_pre_topc @ X21))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.53        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_F)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_F))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.53      inference('split', [status(esa)], ['11'])).
% 0.21/0.53  thf('13', plain, (((sk_E) = (sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_E))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53           sk_F)
% 0.21/0.53        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.21/0.53       ~
% 0.21/0.53       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_F))),
% 0.21/0.53      inference('split', [status(esa)], ['15'])).
% 0.21/0.53  thf('17', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('split', [status(esa)], ['11'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t64_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.53                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.53                             ( r1_tmap_1 @
% 0.21/0.53                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X22)
% 0.21/0.53          | ~ (v2_pre_topc @ X22)
% 0.21/0.53          | ~ (l1_pre_topc @ X22)
% 0.21/0.53          | (v2_struct_0 @ X23)
% 0.21/0.53          | ~ (m1_pre_topc @ X23 @ X22)
% 0.21/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.21/0.53          | (r1_tmap_1 @ X23 @ X25 @ (k2_tmap_1 @ X22 @ X25 @ X26 @ X23) @ X24)
% 0.21/0.53          | ((X27) != (X24))
% 0.21/0.53          | ~ (r1_tmap_1 @ X22 @ X25 @ X26 @ X27)
% 0.21/0.53          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X22))
% 0.21/0.53          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25))))
% 0.21/0.53          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25))
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (l1_pre_topc @ X25)
% 0.21/0.53          | ~ (v2_pre_topc @ X25)
% 0.21/0.53          | (v2_struct_0 @ X25))),
% 0.21/0.53      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X25)
% 0.21/0.53          | ~ (v2_pre_topc @ X25)
% 0.21/0.53          | ~ (l1_pre_topc @ X25)
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25))
% 0.21/0.53          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25))))
% 0.21/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X22))
% 0.21/0.53          | ~ (r1_tmap_1 @ X22 @ X25 @ X26 @ X24)
% 0.21/0.53          | (r1_tmap_1 @ X23 @ X25 @ (k2_tmap_1 @ X22 @ X25 @ X26 @ X23) @ X24)
% 0.21/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.21/0.53          | ~ (m1_pre_topc @ X23 @ X22)
% 0.21/0.53          | (v2_struct_0 @ X23)
% 0.21/0.53          | ~ (l1_pre_topc @ X22)
% 0.21/0.53          | ~ (v2_pre_topc @ X22)
% 0.21/0.53          | (v2_struct_0 @ X22))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.53  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['22', '23', '24', '25', '26', '27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_A)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.53           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53              sk_E)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.53           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '29'])).
% 0.21/0.53  thf('31', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_A)
% 0.21/0.53           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53              sk_E)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.53           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_B)
% 0.21/0.54         | (v2_struct_0 @ sk_D)
% 0.21/0.54         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.54         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '32'])).
% 0.21/0.54  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_B)
% 0.21/0.54         | (v2_struct_0 @ sk_D)
% 0.21/0.54         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54           sk_F))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.54      inference('split', [status(esa)], ['15'])).
% 0.21/0.54  thf('37', plain, (((sk_E) = (sk_F))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54           sk_E))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.54             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.54  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.54             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.54  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_D))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.54             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf('44', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_F)) | 
% 0.21/0.54       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_F)) | 
% 0.21/0.54       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.54      inference('split', [status(esa)], ['11'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_F))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['16', '45', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54        sk_E)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['14', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t66_tmap_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.54             ( l1_pre_topc @ B ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54                 ( m1_subset_1 @
% 0.21/0.54                   C @ 
% 0.21/0.54                   ( k1_zfmisc_1 @
% 0.21/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.54                   ( ![E:$i]:
% 0.21/0.54                     ( ( m1_subset_1 @
% 0.21/0.54                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54                       ( ![F:$i]:
% 0.21/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                           ( ![G:$i]:
% 0.21/0.54                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.54                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.21/0.54                                   ( r2_hidden @ F @ E ) & 
% 0.21/0.54                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.54                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.54                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.54                                   ( r1_tmap_1 @
% 0.21/0.54                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X28)
% 0.21/0.54          | ~ (v2_pre_topc @ X28)
% 0.21/0.54          | ~ (l1_pre_topc @ X28)
% 0.21/0.54          | (v2_struct_0 @ X29)
% 0.21/0.54          | ~ (m1_pre_topc @ X29 @ X28)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.21/0.54          | ~ (v3_pre_topc @ X31 @ X28)
% 0.21/0.54          | ~ (r2_hidden @ X30 @ X31)
% 0.21/0.54          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X29))
% 0.21/0.54          | ((X30) != (X32))
% 0.21/0.54          | ~ (r1_tmap_1 @ X29 @ X33 @ (k2_tmap_1 @ X28 @ X33 @ X34 @ X29) @ 
% 0.21/0.54               X32)
% 0.21/0.54          | (r1_tmap_1 @ X28 @ X33 @ X34 @ X30)
% 0.21/0.54          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.54          | ~ (m1_subset_1 @ X34 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))))
% 0.21/0.54          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))
% 0.21/0.54          | ~ (v1_funct_1 @ X34)
% 0.21/0.54          | ~ (l1_pre_topc @ X33)
% 0.21/0.54          | ~ (v2_pre_topc @ X33)
% 0.21/0.54          | (v2_struct_0 @ X33))),
% 0.21/0.54      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X33)
% 0.21/0.54          | ~ (v2_pre_topc @ X33)
% 0.21/0.54          | ~ (l1_pre_topc @ X33)
% 0.21/0.54          | ~ (v1_funct_1 @ X34)
% 0.21/0.54          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))
% 0.21/0.54          | ~ (m1_subset_1 @ X34 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))))
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.54          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.21/0.54          | (r1_tmap_1 @ X28 @ X33 @ X34 @ X32)
% 0.21/0.54          | ~ (r1_tmap_1 @ X29 @ X33 @ (k2_tmap_1 @ X28 @ X33 @ X34 @ X29) @ 
% 0.21/0.54               X32)
% 0.21/0.54          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X29))
% 0.21/0.54          | ~ (r2_hidden @ X32 @ X31)
% 0.21/0.54          | ~ (v3_pre_topc @ X31 @ X28)
% 0.21/0.54          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.21/0.54          | ~ (m1_pre_topc @ X29 @ X28)
% 0.21/0.54          | (v2_struct_0 @ X29)
% 0.21/0.54          | ~ (l1_pre_topc @ X28)
% 0.21/0.54          | ~ (v2_pre_topc @ X28)
% 0.21/0.54          | (v2_struct_0 @ X28))),
% 0.21/0.54      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.21/0.54          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.54               X1)
% 0.21/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['49', '51'])).
% 0.21/0.54  thf('53', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.21/0.54          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.54               X1)
% 0.21/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['52', '53', '54', '55', '56', '57', '58'])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.54          | ~ (r2_hidden @ sk_E @ X0)
% 0.21/0.54          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ sk_D)
% 0.21/0.54          | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['48', '59'])).
% 0.21/0.54  thf('61', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('62', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('63', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.54          | ~ (r2_hidden @ sk_E @ X0)
% 0.21/0.54          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ sk_D)
% 0.21/0.54          | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)
% 0.21/0.54        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.54        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_D))
% 0.21/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '64'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf(t16_tsep_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.54                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X17 @ X18)
% 0.21/0.54          | ((X19) != (u1_struct_0 @ X17))
% 0.21/0.54          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.21/0.54          | ~ (m1_pre_topc @ X17 @ X18)
% 0.21/0.54          | (v3_pre_topc @ X19 @ X18)
% 0.21/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.54          | ~ (l1_pre_topc @ X18)
% 0.21/0.54          | ~ (v2_pre_topc @ X18))),
% 0.21/0.54      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ X18)
% 0.21/0.54          | ~ (l1_pre_topc @ X18)
% 0.21/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.21/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.54          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.21/0.54          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.21/0.54          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.21/0.54      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      ((~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.54        | ~ (v1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.54        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['66', '68'])).
% 0.21/0.54  thf('70', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('71', plain, ((v1_tsep_1 @ sk_D @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('73', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('74', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.21/0.54  thf(dt_k2_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.54  thf('76', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.54  thf('77', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.54      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('79', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['65', '74', '79'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '80'])).
% 0.21/0.54  thf('82', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.21/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('split', [status(esa)], ['15'])).
% 0.21/0.54  thf('83', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['16', '45'])).
% 0.21/0.54  thf('84', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.21/0.54  thf('85', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['81', '84'])).
% 0.21/0.54  thf(fc2_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (![X13 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.21/0.54          | ~ (l1_struct_0 @ X13)
% 0.21/0.54          | (v2_struct_0 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | ~ (l1_struct_0 @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.54  thf('88', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_m1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.54  thf('89', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.54          | (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (l1_pre_topc @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.54  thf('90', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.54  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('92', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.54  thf(dt_l1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.54  thf('94', plain, ((l1_struct_0 @ sk_D)),
% 0.21/0.54      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.54  thf('95', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D))),
% 0.21/0.54      inference('demod', [status(thm)], ['87', '94'])).
% 0.21/0.54  thf('96', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('simplify', [status(thm)], ['95'])).
% 0.21/0.54  thf('97', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('98', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.21/0.54      inference('clc', [status(thm)], ['96', '97'])).
% 0.21/0.54  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('100', plain, ((v2_struct_0 @ sk_D)),
% 0.21/0.54      inference('clc', [status(thm)], ['98', '99'])).
% 0.21/0.54  thf('101', plain, ($false), inference('demod', [status(thm)], ['0', '100'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
