%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fs0ZMYmEYN

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 313 expanded)
%              Number of leaves         :   34 ( 101 expanded)
%              Depth                    :   26
%              Number of atoms          : 1530 (10136 expanded)
%              Number of equality atoms :   13 ( 149 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

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
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r1_tmap_1 @ X15 @ X17 @ ( k2_tmap_1 @ X14 @ X17 @ X18 @ X15 ) @ X16 )
      | ( X19 != X16 )
      | ~ ( r1_tmap_1 @ X14 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_tmap_1 @ X14 @ X17 @ X18 @ X16 )
      | ( r1_tmap_1 @ X15 @ X17 @ ( k2_tmap_1 @ X14 @ X17 @ X18 @ X15 ) @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( v3_pre_topc @ X23 @ X20 )
      | ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ ( u1_struct_0 @ X21 ) )
      | ( X22 != X24 )
      | ~ ( r1_tmap_1 @ X21 @ X25 @ ( k2_tmap_1 @ X20 @ X25 @ X26 @ X21 ) @ X24 )
      | ( r1_tmap_1 @ X20 @ X25 @ X26 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('51',plain,(
    ! [X20: $i,X21: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X20 @ X25 @ X26 @ X24 )
      | ~ ( r1_tmap_1 @ X21 @ X25 @ ( k2_tmap_1 @ X20 @ X25 @ X26 @ X21 ) @ X24 )
      | ~ ( r1_tarski @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v3_pre_topc @ X23 @ X20 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ~ ( v1_tsep_1 @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v3_pre_topc @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('68',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X9 ) @ X10 )
      | ~ ( v1_tsep_1 @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','74','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','77'])).

thf('79',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['15'])).

thf('80',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['16','45'])).

thf('81',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('83',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('86',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['87','88'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('90',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('91',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['84','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fs0ZMYmEYN
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:31:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 62 iterations in 0.050s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(t67_tmap_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                 ( m1_subset_1 @
% 0.21/0.52                   C @ 
% 0.21/0.52                   ( k1_zfmisc_1 @
% 0.21/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.52                     ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                       ( ![F:$i]:
% 0.21/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                           ( ( ( E ) = ( F ) ) =>
% 0.21/0.52                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.52                               ( r1_tmap_1 @
% 0.21/0.52                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52                ( l1_pre_topc @ B ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52                    ( v1_funct_2 @
% 0.21/0.52                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                    ( m1_subset_1 @
% 0.21/0.52                      C @ 
% 0.21/0.52                      ( k1_zfmisc_1 @
% 0.21/0.52                        ( k2_zfmisc_1 @
% 0.21/0.52                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.52                        ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.52                      ( ![E:$i]:
% 0.21/0.52                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                          ( ![F:$i]:
% 0.21/0.52                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                              ( ( ( E ) = ( F ) ) =>
% 0.21/0.52                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.52                                  ( r1_tmap_1 @
% 0.21/0.52                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.21/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain, (((sk_E) = (sk_F))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf(t2_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         ((r2_hidden @ X3 @ X4)
% 0.21/0.52          | (v1_xboole_0 @ X4)
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t1_tsep_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.52           ( m1_subset_1 @
% 0.21/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X12 @ X13)
% 0.21/0.52          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.52          | ~ (l1_pre_topc @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52         sk_F)
% 0.21/0.52        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52         sk_F))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.52               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.52      inference('split', [status(esa)], ['11'])).
% 0.21/0.52  thf('13', plain, (((sk_E) = (sk_F))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52         sk_E))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.52               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52           sk_F)
% 0.21/0.52        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.21/0.52       ~
% 0.21/0.52       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52         sk_F))),
% 0.21/0.52      inference('split', [status(esa)], ['15'])).
% 0.21/0.52  thf('17', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.52      inference('split', [status(esa)], ['11'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t64_tmap_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                 ( m1_subset_1 @
% 0.21/0.52                   C @ 
% 0.21/0.52                   ( k1_zfmisc_1 @
% 0.21/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                       ( ![F:$i]:
% 0.21/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.52                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.52                             ( r1_tmap_1 @
% 0.21/0.52                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X14)
% 0.21/0.52          | ~ (v2_pre_topc @ X14)
% 0.21/0.52          | ~ (l1_pre_topc @ X14)
% 0.21/0.52          | (v2_struct_0 @ X15)
% 0.21/0.52          | ~ (m1_pre_topc @ X15 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.21/0.52          | (r1_tmap_1 @ X15 @ X17 @ (k2_tmap_1 @ X14 @ X17 @ X18 @ X15) @ X16)
% 0.21/0.52          | ((X19) != (X16))
% 0.21/0.52          | ~ (r1_tmap_1 @ X14 @ X17 @ X18 @ X19)
% 0.21/0.52          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X14))
% 0.21/0.52          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17))))
% 0.21/0.52          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17))
% 0.21/0.52          | ~ (v1_funct_1 @ X18)
% 0.21/0.52          | ~ (l1_pre_topc @ X17)
% 0.21/0.52          | ~ (v2_pre_topc @ X17)
% 0.21/0.52          | (v2_struct_0 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X17)
% 0.21/0.52          | ~ (v2_pre_topc @ X17)
% 0.21/0.52          | ~ (l1_pre_topc @ X17)
% 0.21/0.52          | ~ (v1_funct_1 @ X18)
% 0.21/0.52          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17))
% 0.21/0.52          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17))))
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.21/0.52          | ~ (r1_tmap_1 @ X14 @ X17 @ X18 @ X16)
% 0.21/0.52          | (r1_tmap_1 @ X15 @ X17 @ (k2_tmap_1 @ X14 @ X17 @ X18 @ X15) @ X16)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.21/0.52          | ~ (m1_pre_topc @ X15 @ X14)
% 0.21/0.52          | (v2_struct_0 @ X15)
% 0.21/0.52          | ~ (l1_pre_topc @ X14)
% 0.21/0.52          | ~ (v2_pre_topc @ X14)
% 0.21/0.52          | (v2_struct_0 @ X14))),
% 0.21/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_B)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.52          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.52  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.52          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['22', '23', '24', '25', '26', '27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          ((v2_struct_0 @ sk_A)
% 0.21/0.52           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.52           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.52              sk_E)
% 0.21/0.52           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.52           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.52           | (v2_struct_0 @ X0)
% 0.21/0.52           | (v2_struct_0 @ sk_B)))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '29'])).
% 0.21/0.52  thf('31', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          ((v2_struct_0 @ sk_A)
% 0.21/0.52           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.52              sk_E)
% 0.21/0.52           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.52           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.52           | (v2_struct_0 @ X0)
% 0.21/0.52           | (v2_struct_0 @ sk_B)))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((((v2_struct_0 @ sk_B)
% 0.21/0.52         | (v2_struct_0 @ sk_D)
% 0.21/0.52         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.52         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.52            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.21/0.52         | (v2_struct_0 @ sk_A)))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '32'])).
% 0.21/0.52  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((((v2_struct_0 @ sk_B)
% 0.21/0.52         | (v2_struct_0 @ sk_D)
% 0.21/0.52         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.52            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.21/0.52         | (v2_struct_0 @ sk_A)))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52           sk_F))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.52               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.52      inference('split', [status(esa)], ['15'])).
% 0.21/0.52  thf('37', plain, (((sk_E) = (sk_F))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52           sk_E))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.52               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.52               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.52             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.52  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.52               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.52             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.52      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_D))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.52               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.21/0.52             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.52      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52         sk_F)) | 
% 0.21/0.52       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52         sk_F)) | 
% 0.21/0.52       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.52      inference('split', [status(esa)], ['11'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52         sk_F))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['16', '45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.52        sk_E)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['14', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t66_tmap_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                 ( m1_subset_1 @
% 0.21/0.52                   C @ 
% 0.21/0.52                   ( k1_zfmisc_1 @
% 0.21/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( m1_subset_1 @
% 0.21/0.52                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.52                       ( ![F:$i]:
% 0.21/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                           ( ![G:$i]:
% 0.21/0.52                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.21/0.52                                   ( r2_hidden @ F @ E ) & 
% 0.21/0.52                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.52                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.52                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.52                                   ( r1_tmap_1 @
% 0.21/0.52                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X20)
% 0.21/0.52          | ~ (v2_pre_topc @ X20)
% 0.21/0.52          | ~ (l1_pre_topc @ X20)
% 0.21/0.52          | (v2_struct_0 @ X21)
% 0.21/0.52          | ~ (m1_pre_topc @ X21 @ X20)
% 0.21/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.21/0.52          | ~ (v3_pre_topc @ X23 @ X20)
% 0.21/0.52          | ~ (r2_hidden @ X22 @ X23)
% 0.21/0.52          | ~ (r1_tarski @ X23 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ((X22) != (X24))
% 0.21/0.52          | ~ (r1_tmap_1 @ X21 @ X25 @ (k2_tmap_1 @ X20 @ X25 @ X26 @ X21) @ 
% 0.21/0.52               X24)
% 0.21/0.52          | (r1_tmap_1 @ X20 @ X25 @ X26 @ X22)
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))))
% 0.21/0.52          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))
% 0.21/0.52          | ~ (v1_funct_1 @ X26)
% 0.21/0.52          | ~ (l1_pre_topc @ X25)
% 0.21/0.52          | ~ (v2_pre_topc @ X25)
% 0.21/0.52          | (v2_struct_0 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X25)
% 0.21/0.52          | ~ (v2_pre_topc @ X25)
% 0.21/0.52          | ~ (l1_pre_topc @ X25)
% 0.21/0.52          | ~ (v1_funct_1 @ X26)
% 0.21/0.52          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))))
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X21))
% 0.21/0.52          | (r1_tmap_1 @ X20 @ X25 @ X26 @ X24)
% 0.21/0.52          | ~ (r1_tmap_1 @ X21 @ X25 @ (k2_tmap_1 @ X20 @ X25 @ X26 @ X21) @ 
% 0.21/0.52               X24)
% 0.21/0.52          | ~ (r1_tarski @ X23 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (r2_hidden @ X24 @ X23)
% 0.21/0.52          | ~ (v3_pre_topc @ X23 @ X20)
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X20))
% 0.21/0.52          | ~ (m1_pre_topc @ X21 @ X20)
% 0.21/0.52          | (v2_struct_0 @ X21)
% 0.21/0.52          | ~ (l1_pre_topc @ X20)
% 0.21/0.52          | ~ (v2_pre_topc @ X20)
% 0.21/0.52          | (v2_struct_0 @ X20))),
% 0.21/0.52      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_B)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.21/0.52          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.52               X1)
% 0.21/0.52          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['49', '51'])).
% 0.21/0.52  thf('53', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.21/0.52          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.52               X1)
% 0.21/0.52          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['52', '53', '54', '55', '56', '57', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | ~ (r2_hidden @ sk_E @ X0)
% 0.21/0.52          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '59'])).
% 0.21/0.52  thf('61', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('62', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | ~ (r2_hidden @ sk_E @ X0)
% 0.21/0.52          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)
% 0.21/0.52        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf(t16_tsep_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.52                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.52          | ((X11) != (u1_struct_0 @ X9))
% 0.21/0.52          | ~ (v1_tsep_1 @ X9 @ X10)
% 0.21/0.52          | ~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.52          | (v3_pre_topc @ X11 @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.52          | ~ (l1_pre_topc @ X10)
% 0.21/0.52          | ~ (v2_pre_topc @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (v2_pre_topc @ X10)
% 0.21/0.52          | ~ (l1_pre_topc @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.21/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.52          | (v3_pre_topc @ (u1_struct_0 @ X9) @ X10)
% 0.21/0.52          | ~ (v1_tsep_1 @ X9 @ X10)
% 0.21/0.52          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.21/0.52      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.52        | ~ (v1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.52        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['66', '68'])).
% 0.21/0.52  thf('70', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('71', plain, ((v1_tsep_1 @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('73', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('76', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.52      inference('simplify', [status(thm)], ['75'])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['65', '74', '76'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '77'])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.21/0.52         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.52      inference('split', [status(esa)], ['15'])).
% 0.21/0.52  thf('80', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['16', '45'])).
% 0.21/0.52  thf('81', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['78', '81'])).
% 0.21/0.52  thf(fc2_struct_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (![X8 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.21/0.52          | ~ (l1_struct_0 @ X8)
% 0.21/0.52          | (v2_struct_0 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | ~ (l1_struct_0 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('85', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_m1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('87', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.52  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('89', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.52  thf(dt_l1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.52  thf('90', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('91', plain, ((l1_struct_0 @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['84', '91'])).
% 0.21/0.52  thf('93', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('simplify', [status(thm)], ['92'])).
% 0.21/0.52  thf('94', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('95', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.21/0.52      inference('clc', [status(thm)], ['93', '94'])).
% 0.21/0.52  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('97', plain, ((v2_struct_0 @ sk_D)),
% 0.21/0.52      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.52  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
