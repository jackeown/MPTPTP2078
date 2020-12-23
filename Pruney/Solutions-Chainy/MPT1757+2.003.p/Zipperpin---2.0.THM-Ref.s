%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KuJycTmRR6

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 363 expanded)
%              Number of leaves         :   34 ( 115 expanded)
%              Depth                    :   22
%              Number of atoms          : 1632 (11763 expanded)
%              Number of equality atoms :   13 ( 174 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X26 @ X28 @ ( k2_tmap_1 @ X25 @ X28 @ X29 @ X26 ) @ X27 )
      | ( X30 != X27 )
      | ~ ( r1_tmap_1 @ X25 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_tmap_1 @ X25 @ X28 @ X29 @ X27 )
      | ( r1_tmap_1 @ X26 @ X28 @ ( k2_tmap_1 @ X25 @ X28 @ X29 @ X26 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
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
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['10'])).

thf('34',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['6'])).

thf('44',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['11','42','43'])).

thf('45',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['9','44'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( v3_pre_topc @ X34 @ X31 )
      | ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X32 ) )
      | ( X33 != X35 )
      | ~ ( r1_tmap_1 @ X32 @ X36 @ ( k2_tmap_1 @ X31 @ X36 @ X37 @ X32 ) @ X35 )
      | ( r1_tmap_1 @ X31 @ X36 @ X37 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('48',plain,(
    ! [X31: $i,X32: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X32 ) )
      | ( r1_tmap_1 @ X31 @ X36 @ X37 @ X35 )
      | ~ ( r1_tmap_1 @ X32 @ X36 @ ( k2_tmap_1 @ X31 @ X36 @ X37 @ X32 ) @ X35 )
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r2_hidden @ X35 @ X34 )
      | ~ ( v3_pre_topc @ X34 @ X31 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
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
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
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
    inference(demod,[status(thm)],['49','50','51','52','53','54','55'])).

thf('57',plain,(
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
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','61'])).

thf('63',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('64',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( X22
       != ( u1_struct_0 @ X20 ) )
      | ~ ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X20 ) @ X21 )
      | ~ ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_tsep_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('73',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( r2_hidden @ X18 @ ( k1_connsp_2 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('76',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('77',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['74','80','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('90',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('91',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('93',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['83','84'])).

thf('94',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('97',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','98'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','71','99','101'])).

thf('103',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['10'])).

thf('104',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['11','42'])).

thf('105',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['0','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KuJycTmRR6
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 77 iterations in 0.044s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(t67_tmap_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.51                     ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.51                   ( ![E:$i]:
% 0.21/0.51                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                       ( ![F:$i]:
% 0.21/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.51                           ( ( ( E ) = ( F ) ) =>
% 0.21/0.51                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.51                               ( r1_tmap_1 @
% 0.21/0.51                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51                ( l1_pre_topc @ B ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                    ( v1_funct_2 @
% 0.21/0.51                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                    ( m1_subset_1 @
% 0.21/0.51                      C @ 
% 0.21/0.51                      ( k1_zfmisc_1 @
% 0.21/0.51                        ( k2_zfmisc_1 @
% 0.21/0.51                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.51                        ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.51                      ( ![E:$i]:
% 0.21/0.51                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                          ( ![F:$i]:
% 0.21/0.51                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.51                              ( ( ( E ) = ( F ) ) =>
% 0.21/0.51                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.51                                  ( r1_tmap_1 @
% 0.21/0.51                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t1_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( m1_subset_1 @
% 0.21/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X23 @ X24)
% 0.21/0.51          | (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.51          | ~ (l1_pre_topc @ X24))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51         sk_F)
% 0.21/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51         sk_F))
% 0.21/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.51      inference('split', [status(esa)], ['6'])).
% 0.21/0.51  thf('8', plain, (((sk_E) = (sk_F))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51         sk_E))
% 0.21/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51           sk_F)
% 0.21/0.51        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.21/0.51       ~
% 0.21/0.51       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51         sk_F))),
% 0.21/0.51      inference('split', [status(esa)], ['10'])).
% 0.21/0.51  thf('12', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, (((sk_E) = (sk_F))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.21/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.51      inference('split', [status(esa)], ['6'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t64_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.51                   ( ![E:$i]:
% 0.21/0.51                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                       ( ![F:$i]:
% 0.21/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.51                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.51                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.51                             ( r1_tmap_1 @
% 0.21/0.51                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X25)
% 0.21/0.51          | ~ (v2_pre_topc @ X25)
% 0.21/0.51          | ~ (l1_pre_topc @ X25)
% 0.21/0.51          | (v2_struct_0 @ X26)
% 0.21/0.51          | ~ (m1_pre_topc @ X26 @ X25)
% 0.21/0.51          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.21/0.51          | (r1_tmap_1 @ X26 @ X28 @ (k2_tmap_1 @ X25 @ X28 @ X29 @ X26) @ X27)
% 0.21/0.51          | ((X30) != (X27))
% 0.21/0.51          | ~ (r1_tmap_1 @ X25 @ X28 @ X29 @ X30)
% 0.21/0.51          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X25))
% 0.21/0.51          | ~ (m1_subset_1 @ X29 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X28))))
% 0.21/0.51          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X28))
% 0.21/0.51          | ~ (v1_funct_1 @ X29)
% 0.21/0.51          | ~ (l1_pre_topc @ X28)
% 0.21/0.51          | ~ (v2_pre_topc @ X28)
% 0.21/0.51          | (v2_struct_0 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X28)
% 0.21/0.51          | ~ (v2_pre_topc @ X28)
% 0.21/0.51          | ~ (l1_pre_topc @ X28)
% 0.21/0.51          | ~ (v1_funct_1 @ X29)
% 0.21/0.51          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X28))
% 0.21/0.51          | ~ (m1_subset_1 @ X29 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X28))))
% 0.21/0.51          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.21/0.51          | ~ (r1_tmap_1 @ X25 @ X28 @ X29 @ X27)
% 0.21/0.51          | (r1_tmap_1 @ X26 @ X28 @ (k2_tmap_1 @ X25 @ X28 @ X29 @ X26) @ X27)
% 0.21/0.51          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.21/0.51          | ~ (m1_pre_topc @ X26 @ X25)
% 0.21/0.51          | (v2_struct_0 @ X26)
% 0.21/0.51          | ~ (l1_pre_topc @ X25)
% 0.21/0.51          | ~ (v2_pre_topc @ X25)
% 0.21/0.51          | (v2_struct_0 @ X25))),
% 0.21/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.51          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.51  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.51          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['19', '20', '21', '22', '23', '24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          ((v2_struct_0 @ sk_A)
% 0.21/0.51           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.51           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.51              sk_E)
% 0.21/0.51           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.51           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.51           | (v2_struct_0 @ X0)
% 0.21/0.51           | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '26'])).
% 0.21/0.51  thf('28', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          ((v2_struct_0 @ sk_A)
% 0.21/0.51           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.51              sk_E)
% 0.21/0.51           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.51           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.51           | (v2_struct_0 @ X0)
% 0.21/0.51           | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B)
% 0.21/0.51         | (v2_struct_0 @ sk_D)
% 0.21/0.51         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.51            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.21/0.51         | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '29'])).
% 0.21/0.51  thf('31', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B)
% 0.21/0.51         | (v2_struct_0 @ sk_D)
% 0.21/0.51         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.51            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.21/0.51         | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51           sk_F))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.51      inference('split', [status(esa)], ['10'])).
% 0.21/0.51  thf('34', plain, (((sk_E) = (sk_F))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51           sk_E))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.51             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.51  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.51             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.51      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_D))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.51             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51         sk_F)) | 
% 0.21/0.51       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51         sk_F)) | 
% 0.21/0.51       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.51      inference('split', [status(esa)], ['6'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51         sk_F))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['11', '42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.51        sk_E)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['9', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t66_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.51                   ( ![E:$i]:
% 0.21/0.51                     ( ( m1_subset_1 @
% 0.21/0.51                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                       ( ![F:$i]:
% 0.21/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                           ( ![G:$i]:
% 0.21/0.51                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.51                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.21/0.51                                   ( r2_hidden @ F @ E ) & 
% 0.21/0.51                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.51                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.51                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.51                                   ( r1_tmap_1 @
% 0.21/0.51                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X31)
% 0.21/0.51          | ~ (v2_pre_topc @ X31)
% 0.21/0.51          | ~ (l1_pre_topc @ X31)
% 0.21/0.51          | (v2_struct_0 @ X32)
% 0.21/0.51          | ~ (m1_pre_topc @ X32 @ X31)
% 0.21/0.51          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.21/0.51          | ~ (v3_pre_topc @ X34 @ X31)
% 0.21/0.51          | ~ (r2_hidden @ X33 @ X34)
% 0.21/0.51          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X32))
% 0.21/0.51          | ((X33) != (X35))
% 0.21/0.51          | ~ (r1_tmap_1 @ X32 @ X36 @ (k2_tmap_1 @ X31 @ X36 @ X37 @ X32) @ 
% 0.21/0.51               X35)
% 0.21/0.51          | (r1_tmap_1 @ X31 @ X36 @ X37 @ X33)
% 0.21/0.51          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X32))
% 0.21/0.51          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.21/0.51          | ~ (m1_subset_1 @ X37 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X36))))
% 0.21/0.51          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X36))
% 0.21/0.51          | ~ (v1_funct_1 @ X37)
% 0.21/0.51          | ~ (l1_pre_topc @ X36)
% 0.21/0.51          | ~ (v2_pre_topc @ X36)
% 0.21/0.51          | (v2_struct_0 @ X36))),
% 0.21/0.51      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X31 : $i, X32 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X36)
% 0.21/0.51          | ~ (v2_pre_topc @ X36)
% 0.21/0.51          | ~ (l1_pre_topc @ X36)
% 0.21/0.51          | ~ (v1_funct_1 @ X37)
% 0.21/0.51          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X36))
% 0.21/0.51          | ~ (m1_subset_1 @ X37 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X36))))
% 0.21/0.51          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.21/0.51          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X32))
% 0.21/0.51          | (r1_tmap_1 @ X31 @ X36 @ X37 @ X35)
% 0.21/0.51          | ~ (r1_tmap_1 @ X32 @ X36 @ (k2_tmap_1 @ X31 @ X36 @ X37 @ X32) @ 
% 0.21/0.51               X35)
% 0.21/0.51          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X32))
% 0.21/0.51          | ~ (r2_hidden @ X35 @ X34)
% 0.21/0.51          | ~ (v3_pre_topc @ X34 @ X31)
% 0.21/0.51          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X31))
% 0.21/0.51          | ~ (m1_pre_topc @ X32 @ X31)
% 0.21/0.51          | (v2_struct_0 @ X32)
% 0.21/0.51          | ~ (l1_pre_topc @ X31)
% 0.21/0.51          | ~ (v2_pre_topc @ X31)
% 0.21/0.51          | (v2_struct_0 @ X31))),
% 0.21/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.21/0.51          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.51               X1)
% 0.21/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '48'])).
% 0.21/0.51  thf('50', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.21/0.51          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.51               X1)
% 0.21/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['49', '50', '51', '52', '53', '54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.51          | ~ (r2_hidden @ sk_E @ X0)
% 0.21/0.51          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ sk_D)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '56'])).
% 0.21/0.51  thf('58', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('59', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.51          | ~ (r2_hidden @ sk_E @ X0)
% 0.21/0.51          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ sk_D)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_D)
% 0.21/0.51        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)
% 0.21/0.51        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.51        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_D))
% 0.21/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '61'])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf(t16_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.51                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.51          | ((X22) != (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (v1_tsep_1 @ X20 @ X21)
% 0.21/0.51          | ~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.51          | (v3_pre_topc @ X22 @ X21)
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.51          | ~ (l1_pre_topc @ X21)
% 0.21/0.51          | ~ (v2_pre_topc @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (v2_pre_topc @ X21)
% 0.21/0.51          | ~ (l1_pre_topc @ X21)
% 0.21/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.21/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.51          | (v3_pre_topc @ (u1_struct_0 @ X20) @ X21)
% 0.21/0.51          | ~ (v1_tsep_1 @ X20 @ X21)
% 0.21/0.51          | ~ (m1_pre_topc @ X20 @ X21))),
% 0.21/0.51      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      ((~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.51        | ~ (v1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.51        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['63', '65'])).
% 0.21/0.51  thf('67', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('68', plain, ((v1_tsep_1 @ sk_D @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('71', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.21/0.51  thf('72', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf(t30_connsp_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.21/0.51          | (r2_hidden @ X18 @ (k1_connsp_2 @ X19 @ X18))
% 0.21/0.51          | ~ (l1_pre_topc @ X19)
% 0.21/0.51          | ~ (v2_pre_topc @ X19)
% 0.21/0.51          | (v2_struct_0 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_D)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_D)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_D)
% 0.21/0.51        | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D @ sk_E)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.51  thf('75', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.51          | (v2_pre_topc @ X9)
% 0.21/0.51          | ~ (l1_pre_topc @ X10)
% 0.21/0.51          | ~ (v2_pre_topc @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.51  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('80', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.21/0.51  thf('81', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.51          | (l1_pre_topc @ X11)
% 0.21/0.51          | ~ (l1_pre_topc @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('83', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('85', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_D) | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D @ sk_E)))),
% 0.21/0.51      inference('demod', [status(thm)], ['74', '80', '85'])).
% 0.21/0.51  thf('87', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('88', plain, ((r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D @ sk_E))),
% 0.21/0.51      inference('clc', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('89', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf(dt_k1_connsp_2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X16)
% 0.21/0.51          | ~ (v2_pre_topc @ X16)
% 0.21/0.51          | (v2_struct_0 @ X16)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.51          | (m1_subset_1 @ (k1_connsp_2 @ X16 @ X17) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_connsp_2 @ sk_D @ sk_E) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.51        | (v2_struct_0 @ sk_D)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_D)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.51  thf('92', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.21/0.51  thf('93', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      (((m1_subset_1 @ (k1_connsp_2 @ sk_D @ sk_E) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.51        | (v2_struct_0 @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.21/0.51  thf('95', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      ((m1_subset_1 @ (k1_connsp_2 @ sk_D @ sk_E) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf(l3_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.51          | (r2_hidden @ X3 @ X5)
% 0.21/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_D @ sk_E)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.51  thf('99', plain, ((r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['88', '98'])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('101', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['100'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_D)
% 0.21/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['62', '71', '99', '101'])).
% 0.21/0.51  thf('103', plain,
% 0.21/0.51      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.21/0.51         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.51      inference('split', [status(esa)], ['10'])).
% 0.21/0.51  thf('104', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['11', '42'])).
% 0.21/0.51  thf('105', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['103', '104'])).
% 0.21/0.51  thf('106', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['102', '105'])).
% 0.21/0.51  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('108', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['106', '107'])).
% 0.21/0.51  thf('109', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('110', plain, ((v2_struct_0 @ sk_D)),
% 0.21/0.51      inference('clc', [status(thm)], ['108', '109'])).
% 0.21/0.51  thf('111', plain, ($false), inference('demod', [status(thm)], ['0', '110'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
