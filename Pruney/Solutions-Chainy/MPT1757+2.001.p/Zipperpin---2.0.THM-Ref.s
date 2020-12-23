%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8F7OwNVDsX

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 421 expanded)
%              Number of leaves         :   40 ( 133 expanded)
%              Depth                    :   27
%              Number of atoms          : 1909 (13101 expanded)
%              Number of equality atoms :   13 ( 191 expanded)
%              Maximal formula depth    :   28 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X25 )
      | ~ ( r2_hidden @ X26 @ X24 )
      | ( m1_connsp_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( X29
       != ( u1_struct_0 @ X27 ) )
      | ~ ( v1_tsep_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v3_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X27 ) @ X28 )
      | ~ ( v1_tsep_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_B_1 )
    | ~ ( v1_tsep_1 @ sk_D @ sk_B_1 )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_tsep_1 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B_1 ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('32',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('39',plain,
    ( ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['32'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('41',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( r1_tmap_1 @ X36 @ X38 @ ( k2_tmap_1 @ X35 @ X38 @ X39 @ X36 ) @ X37 )
      | ( X40 != X37 )
      | ~ ( r1_tmap_1 @ X35 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('42',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tmap_1 @ X35 @ X38 @ X39 @ X37 )
      | ( r1_tmap_1 @ X36 @ X38 @ ( k2_tmap_1 @ X35 @ X38 @ X39 @ X36 ) @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B_1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['36'])).

thf('58',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['32'])).

thf('68',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['37','66','67'])).

thf('69',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['35','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('71',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ( v2_struct_0 @ X42 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r1_tarski @ X44 @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_connsp_2 @ X44 @ X41 @ X43 )
      | ( X43 != X45 )
      | ~ ( r1_tmap_1 @ X42 @ X46 @ ( k2_tmap_1 @ X41 @ X46 @ X47 @ X42 ) @ X45 )
      | ( r1_tmap_1 @ X41 @ X46 @ X47 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('72',plain,(
    ! [X41: $i,X42: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X42 ) )
      | ( r1_tmap_1 @ X41 @ X46 @ X47 @ X45 )
      | ~ ( r1_tmap_1 @ X42 @ X46 @ ( k2_tmap_1 @ X41 @ X46 @ X47 @ X42 ) @ X45 )
      | ~ ( m1_connsp_2 @ X44 @ X41 @ X45 )
      | ~ ( r1_tarski @ X44 @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B_1 @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B_1 @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','85'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','89'])).

thf('91',plain,
    ( ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['36'])).

thf('92',plain,(
    ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['37','66'])).

thf('93',plain,(
    ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['87'])).

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

thf('97',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X34 ) )
      | ( m1_pre_topc @ X32 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['100','101','102'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('104',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('105',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('109',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('110',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['110','111'])).

thf('114',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('115',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('116',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['107','112','113','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ ( sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('123',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('124',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['94','124'])).

thf('126',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('129',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['110','111'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['0','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8F7OwNVDsX
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 120 iterations in 0.068s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
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
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         ((r2_hidden @ X5 @ X6)
% 0.21/0.53          | (v1_xboole_0 @ X6)
% 0.21/0.53          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.53        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t1_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( m1_subset_1 @
% 0.21/0.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X30 @ X31)
% 0.21/0.53          | (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.21/0.53          | ~ (l1_pre_topc @ X31))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(t5_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.21/0.53                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.53          | ~ (v3_pre_topc @ X24 @ X25)
% 0.21/0.53          | ~ (r2_hidden @ X26 @ X24)
% 0.21/0.53          | (m1_connsp_2 @ X24 @ X25 @ X26)
% 0.21/0.53          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.21/0.53          | ~ (l1_pre_topc @ X25)
% 0.21/0.53          | ~ (v2_pre_topc @ X25)
% 0.21/0.53          | (v2_struct_0 @ X25))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B_1)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B_1)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.53          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.53          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(t16_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.54                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X27 @ X28)
% 0.21/0.54          | ((X29) != (u1_struct_0 @ X27))
% 0.21/0.54          | ~ (v1_tsep_1 @ X27 @ X28)
% 0.21/0.54          | ~ (m1_pre_topc @ X27 @ X28)
% 0.21/0.54          | (v3_pre_topc @ X29 @ X28)
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.54          | ~ (l1_pre_topc @ X28)
% 0.21/0.54          | ~ (v2_pre_topc @ X28))),
% 0.21/0.54      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ X28)
% 0.21/0.54          | ~ (l1_pre_topc @ X28)
% 0.21/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.21/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.54          | (v3_pre_topc @ (u1_struct_0 @ X27) @ X28)
% 0.21/0.54          | ~ (v1_tsep_1 @ X27 @ X28)
% 0.21/0.54          | ~ (m1_pre_topc @ X27 @ X28))),
% 0.21/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      ((~ (m1_pre_topc @ sk_D @ sk_B_1)
% 0.21/0.54        | ~ (v1_tsep_1 @ sk_D @ sk_B_1)
% 0.21/0.54        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B_1)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.54  thf('21', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain, ((v1_tsep_1 @ sk_D @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('23', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('24', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('25', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B_1)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.54        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '26'])).
% 0.21/0.54  thf('28', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (((m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E)
% 0.21/0.54        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D)))),
% 0.21/0.54      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.54        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_F)
% 0.21/0.54        | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_F))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.54      inference('split', [status(esa)], ['32'])).
% 0.21/0.54  thf('34', plain, (((sk_E) = (sk_F))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_E))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)
% 0.21/0.54        | ~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (~ ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)) | 
% 0.21/0.54       ~
% 0.21/0.54       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_F))),
% 0.21/0.54      inference('split', [status(esa)], ['36'])).
% 0.21/0.54  thf('38', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('split', [status(esa)], ['32'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t64_tmap_1, axiom,
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
% 0.21/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                       ( ![F:$i]:
% 0.21/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.54                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.54                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.54                             ( r1_tmap_1 @
% 0.21/0.54                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X35)
% 0.21/0.54          | ~ (v2_pre_topc @ X35)
% 0.21/0.54          | ~ (l1_pre_topc @ X35)
% 0.21/0.54          | (v2_struct_0 @ X36)
% 0.21/0.54          | ~ (m1_pre_topc @ X36 @ X35)
% 0.21/0.54          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.21/0.54          | (r1_tmap_1 @ X36 @ X38 @ (k2_tmap_1 @ X35 @ X38 @ X39 @ X36) @ X37)
% 0.21/0.54          | ((X40) != (X37))
% 0.21/0.54          | ~ (r1_tmap_1 @ X35 @ X38 @ X39 @ X40)
% 0.21/0.54          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X35))
% 0.21/0.54          | ~ (m1_subset_1 @ X39 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X38))))
% 0.21/0.54          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X38))
% 0.21/0.54          | ~ (v1_funct_1 @ X39)
% 0.21/0.54          | ~ (l1_pre_topc @ X38)
% 0.21/0.54          | ~ (v2_pre_topc @ X38)
% 0.21/0.54          | (v2_struct_0 @ X38))),
% 0.21/0.54      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X38)
% 0.21/0.54          | ~ (v2_pre_topc @ X38)
% 0.21/0.54          | ~ (l1_pre_topc @ X38)
% 0.21/0.54          | ~ (v1_funct_1 @ X39)
% 0.21/0.54          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X38))
% 0.21/0.54          | ~ (m1_subset_1 @ X39 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X38))))
% 0.21/0.54          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.21/0.54          | ~ (r1_tmap_1 @ X35 @ X38 @ X39 @ X37)
% 0.21/0.54          | (r1_tmap_1 @ X36 @ X38 @ (k2_tmap_1 @ X35 @ X38 @ X39 @ X36) @ X37)
% 0.21/0.54          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.21/0.54          | ~ (m1_pre_topc @ X36 @ X35)
% 0.21/0.54          | (v2_struct_0 @ X36)
% 0.21/0.54          | ~ (l1_pre_topc @ X35)
% 0.21/0.54          | ~ (v2_pre_topc @ X35)
% 0.21/0.54          | (v2_struct_0 @ X35))),
% 0.21/0.54      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B_1)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_B_1)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.21/0.54             X1)
% 0.21/0.54          | ~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '42'])).
% 0.21/0.54  thf('44', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B_1)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.21/0.54             X1)
% 0.21/0.54          | ~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['43', '44', '45', '46', '47', '48', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          ((v2_struct_0 @ sk_A)
% 0.21/0.54           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.54              (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ sk_E)
% 0.21/0.54           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.54           | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.21/0.54           | (v2_struct_0 @ X0)
% 0.21/0.54           | (v2_struct_0 @ sk_B_1)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '50'])).
% 0.21/0.54  thf('52', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          ((v2_struct_0 @ sk_A)
% 0.21/0.54           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.54              (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ sk_E)
% 0.21/0.54           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.54           | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.21/0.54           | (v2_struct_0 @ X0)
% 0.21/0.54           | (v2_struct_0 @ sk_B_1)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_B_1)
% 0.21/0.54         | (v2_struct_0 @ sk_D)
% 0.21/0.54         | ~ (m1_pre_topc @ sk_D @ sk_B_1)
% 0.21/0.54         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54            (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '53'])).
% 0.21/0.54  thf('55', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_B_1)
% 0.21/0.54         | (v2_struct_0 @ sk_D)
% 0.21/0.54         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54            (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.54      inference('split', [status(esa)], ['36'])).
% 0.21/0.54  thf('58', plain, (((sk_E) = (sk_F))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_E))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.54      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.54             ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['56', '59'])).
% 0.21/0.54  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_D)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.54             ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf('63', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_D))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.54             ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('65', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_F)) | 
% 0.21/0.54       ~ ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.21/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_F)) | 
% 0.21/0.54       ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.21/0.54      inference('split', [status(esa)], ['32'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54         sk_F))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['37', '66', '67'])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.54        sk_E)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['35', '68'])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t65_tmap_1, axiom,
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
% 0.21/0.54                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.54                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.21/0.54                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.54                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.54                                   ( r1_tmap_1 @
% 0.21/0.54                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X41)
% 0.21/0.54          | ~ (v2_pre_topc @ X41)
% 0.21/0.54          | ~ (l1_pre_topc @ X41)
% 0.21/0.54          | (v2_struct_0 @ X42)
% 0.21/0.54          | ~ (m1_pre_topc @ X42 @ X41)
% 0.21/0.54          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X41))
% 0.21/0.54          | ~ (r1_tarski @ X44 @ (u1_struct_0 @ X42))
% 0.21/0.54          | ~ (m1_connsp_2 @ X44 @ X41 @ X43)
% 0.21/0.54          | ((X43) != (X45))
% 0.21/0.54          | ~ (r1_tmap_1 @ X42 @ X46 @ (k2_tmap_1 @ X41 @ X46 @ X47 @ X42) @ 
% 0.21/0.54               X45)
% 0.21/0.54          | (r1_tmap_1 @ X41 @ X46 @ X47 @ X43)
% 0.21/0.54          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X42))
% 0.21/0.54          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.54          | ~ (m1_subset_1 @ X47 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X46))))
% 0.21/0.54          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X46))
% 0.21/0.54          | ~ (v1_funct_1 @ X47)
% 0.21/0.54          | ~ (l1_pre_topc @ X46)
% 0.21/0.54          | ~ (v2_pre_topc @ X46)
% 0.21/0.54          | (v2_struct_0 @ X46))),
% 0.21/0.54      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      (![X41 : $i, X42 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X46)
% 0.21/0.54          | ~ (v2_pre_topc @ X46)
% 0.21/0.54          | ~ (l1_pre_topc @ X46)
% 0.21/0.54          | ~ (v1_funct_1 @ X47)
% 0.21/0.54          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X46))
% 0.21/0.54          | ~ (m1_subset_1 @ X47 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X46))))
% 0.21/0.54          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.54          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X42))
% 0.21/0.54          | (r1_tmap_1 @ X41 @ X46 @ X47 @ X45)
% 0.21/0.54          | ~ (r1_tmap_1 @ X42 @ X46 @ (k2_tmap_1 @ X41 @ X46 @ X47 @ X42) @ 
% 0.21/0.54               X45)
% 0.21/0.54          | ~ (m1_connsp_2 @ X44 @ X41 @ X45)
% 0.21/0.54          | ~ (r1_tarski @ X44 @ (u1_struct_0 @ X42))
% 0.21/0.54          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X41))
% 0.21/0.54          | ~ (m1_pre_topc @ X42 @ X41)
% 0.21/0.54          | (v2_struct_0 @ X42)
% 0.21/0.54          | ~ (l1_pre_topc @ X41)
% 0.21/0.54          | ~ (v2_pre_topc @ X41)
% 0.21/0.54          | (v2_struct_0 @ X41))),
% 0.21/0.54      inference('simplify', [status(thm)], ['71'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B_1)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_B_1)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B_1 @ X1)
% 0.21/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.54          | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.54          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['70', '72'])).
% 0.21/0.54  thf('74', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('75', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B_1)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B_1 @ X1)
% 0.21/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.54          | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['73', '74', '75', '76', '77', '78', '79'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.54          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.54          | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.21/0.54          | ~ (m1_connsp_2 @ X0 @ sk_B_1 @ sk_E)
% 0.21/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.54          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))
% 0.21/0.54          | ~ (m1_pre_topc @ sk_D @ sk_B_1)
% 0.21/0.54          | (v2_struct_0 @ sk_D)
% 0.21/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['69', '80'])).
% 0.21/0.54  thf('82', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('83', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('84', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('85', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.54          | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.21/0.54          | ~ (m1_connsp_2 @ X0 @ sk_B_1 @ sk_E)
% 0.21/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.54          | (v2_struct_0 @ sk_D)
% 0.21/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_D))
% 0.21/0.54        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E)
% 0.21/0.54        | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '85'])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('88', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.54      inference('simplify', [status(thm)], ['87'])).
% 0.21/0.54  thf('89', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E)
% 0.21/0.54        | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['86', '88'])).
% 0.21/0.54  thf('90', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '89'])).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))
% 0.21/0.54         <= (~ ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.54      inference('split', [status(esa)], ['36'])).
% 0.21/0.54  thf('92', plain, (~ ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['37', '66'])).
% 0.21/0.54  thf('93', plain, (~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 0.21/0.54  thf('94', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['90', '93'])).
% 0.21/0.54  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('96', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.54      inference('simplify', [status(thm)], ['87'])).
% 0.21/0.54  thf(t4_tsep_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.54               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.21/0.54                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.54  thf('97', plain,
% 0.21/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X32 @ X33)
% 0.21/0.54          | ~ (r1_tarski @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X34))
% 0.21/0.54          | (m1_pre_topc @ X32 @ X34)
% 0.21/0.54          | ~ (m1_pre_topc @ X34 @ X33)
% 0.21/0.54          | ~ (l1_pre_topc @ X33)
% 0.21/0.54          | ~ (v2_pre_topc @ X33))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.21/0.54  thf('98', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ X1)
% 0.21/0.54          | ~ (l1_pre_topc @ X1)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.54          | (m1_pre_topc @ X0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.54  thf('99', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((m1_pre_topc @ X0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.54          | ~ (l1_pre_topc @ X1)
% 0.21/0.54          | ~ (v2_pre_topc @ X1))),
% 0.21/0.54      inference('simplify', [status(thm)], ['98'])).
% 0.21/0.54  thf('100', plain,
% 0.21/0.54      ((~ (v2_pre_topc @ sk_B_1)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.54        | (m1_pre_topc @ sk_D @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['95', '99'])).
% 0.21/0.54  thf('101', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('102', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('103', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.21/0.54  thf(rc3_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ?[B:$i]:
% 0.21/0.54         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.21/0.54           ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.54           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('104', plain,
% 0.21/0.54      (![X20 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (sk_B @ X20) @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.54          | ~ (l1_pre_topc @ X20)
% 0.21/0.54          | ~ (v2_pre_topc @ X20)
% 0.21/0.54          | (v2_struct_0 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.21/0.54  thf(t39_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('105', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.54          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.54          | ~ (l1_pre_topc @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.21/0.54  thf('106', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X1)
% 0.21/0.54          | (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.54  thf('107', plain,
% 0.21/0.54      (((m1_subset_1 @ (sk_B @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_D)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_D)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['103', '106'])).
% 0.21/0.54  thf('108', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_m1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.54  thf('109', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X12 @ X13)
% 0.21/0.54          | (l1_pre_topc @ X12)
% 0.21/0.54          | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.54  thf('110', plain, ((~ (l1_pre_topc @ sk_B_1) | (l1_pre_topc @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.54  thf('111', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('112', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['110', '111'])).
% 0.21/0.54  thf('113', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['110', '111'])).
% 0.21/0.54  thf('114', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.54  thf('115', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.54          | (v2_pre_topc @ X10)
% 0.21/0.54          | ~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (v2_pre_topc @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.54  thf('116', plain,
% 0.21/0.54      ((~ (v2_pre_topc @ sk_B_1)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.54        | (v2_pre_topc @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['114', '115'])).
% 0.21/0.54  thf('117', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('118', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('119', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.21/0.54  thf('120', plain,
% 0.21/0.54      (((m1_subset_1 @ (sk_B @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.54        | (v2_struct_0 @ sk_D))),
% 0.21/0.54      inference('demod', [status(thm)], ['107', '112', '113', '119'])).
% 0.21/0.54  thf('121', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('122', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_B @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.54      inference('clc', [status(thm)], ['120', '121'])).
% 0.21/0.54  thf(cc1_subset_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.54  thf('123', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.54          | (v1_xboole_0 @ X3)
% 0.21/0.54          | ~ (v1_xboole_0 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.54  thf('124', plain,
% 0.21/0.54      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_D)) | (v1_xboole_0 @ (sk_B @ sk_D)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['122', '123'])).
% 0.21/0.54  thf('125', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v1_xboole_0 @ (sk_B @ sk_D)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['94', '124'])).
% 0.21/0.54  thf('126', plain,
% 0.21/0.54      (![X20 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (sk_B @ X20))
% 0.21/0.54          | ~ (l1_pre_topc @ X20)
% 0.21/0.54          | ~ (v2_pre_topc @ X20)
% 0.21/0.54          | (v2_struct_0 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.21/0.54  thf('127', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_D)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['125', '126'])).
% 0.21/0.54  thf('128', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.21/0.54  thf('129', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['110', '111'])).
% 0.21/0.54  thf('130', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_D)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_D))),
% 0.21/0.54      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.21/0.54  thf('131', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('simplify', [status(thm)], ['130'])).
% 0.21/0.54  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('133', plain, (((v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_D))),
% 0.21/0.54      inference('clc', [status(thm)], ['131', '132'])).
% 0.21/0.54  thf('134', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('135', plain, ((v2_struct_0 @ sk_D)),
% 0.21/0.54      inference('clc', [status(thm)], ['133', '134'])).
% 0.21/0.54  thf('136', plain, ($false), inference('demod', [status(thm)], ['0', '135'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
