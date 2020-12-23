%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKNoFS2xOy

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:10 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  220 (1274 expanded)
%              Number of leaves         :   36 ( 363 expanded)
%              Depth                    :   22
%              Number of atoms          : 2725 (70501 expanded)
%              Number of equality atoms :   61 ( 834 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(t80_tmap_1,conjecture,(
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
                         => ! [G: $i] :
                              ( ( ( v1_funct_1 @ G )
                                & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( ( D = A )
                                  & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                               => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ! [G: $i] :
                                ( ( ( v1_funct_1 @ G )
                                  & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                  & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                               => ( ( ( D = A )
                                    & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                                 => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                  <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_tmap_1])).

thf('0',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ( X24 = X28 )
      | ~ ( r1_funct_2 @ X25 @ X26 @ X29 @ X27 @ X24 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X17 ) ) )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( r1_tarski @ sk_G @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X17 ) ) )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( r1_tarski @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ~ ( r1_tarski @ X0 @ sk_E )
      | ( X0 = sk_E ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_E = sk_G )
    | ( sk_G = sk_E )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,(
    sk_E = sk_G ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X35 @ X37 )
      | ( ( k3_tmap_1 @ X36 @ X34 @ X37 @ X35 @ X38 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X34 ) @ X38 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('53',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['56','59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('71',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('72',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( ( k2_tmap_1 @ X32 @ X30 @ X33 @ X31 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ X33 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('75',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('78',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['69','85'])).

thf('87',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','41','86'])).

thf('88',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['69','85'])).

thf('90',plain,(
    sk_E = sk_G ),
    inference(simplify,[status(thm)],['40'])).

thf('91',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['90','94'])).

thf('96',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('97',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['45','46'])).

thf('98',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('99',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X39 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X40 @ X42 @ X41 @ X39 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('102',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['97','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('108',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['112','113'])).

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

thf('115',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_funct_2 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('118',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['45','46'])).

thf('119',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('120',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X39 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X40 @ X42 @ X41 @ X39 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('123',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['118','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('129',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['117','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('137',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['45','46'])).

thf('138',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('139',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X39 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X40 @ X42 @ X41 @ X39 @ X43 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('142',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('148',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['136','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','135','154'])).

thf('156',plain,
    ( ( ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
        = sk_F ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['95','155'])).

thf('157',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['89','160'])).

thf('162',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('163',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_F @ sk_F )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_funct_2 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('168',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_funct_2 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['166','168'])).

thf('170',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['165','172'])).

thf('174',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['88','173'])).

thf('175',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['87','174'])).

thf('176',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['91'])).

thf('177',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['91'])).

thf('180',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['88','173','179'])).

thf('181',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['178','180'])).

thf('182',plain,(
    $false ),
    inference(demod,[status(thm)],['175','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKNoFS2xOy
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.65/1.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.85  % Solved by: fo/fo7.sh
% 1.65/1.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.85  % done 1847 iterations in 1.388s
% 1.65/1.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.85  % SZS output start Refutation
% 1.65/1.85  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 1.65/1.85  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.65/1.85  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.65/1.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.65/1.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.85  thf(sk_F_type, type, sk_F: $i).
% 1.65/1.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.65/1.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.65/1.85  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.65/1.85  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.65/1.85  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.85  thf(sk_D_type, type, sk_D: $i).
% 1.65/1.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.65/1.85  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.65/1.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.65/1.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.65/1.85  thf(sk_E_type, type, sk_E: $i).
% 1.65/1.85  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.65/1.85  thf(sk_G_type, type, sk_G: $i).
% 1.65/1.85  thf(t80_tmap_1, conjecture,
% 1.65/1.85    (![A:$i]:
% 1.65/1.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.65/1.85       ( ![B:$i]:
% 1.65/1.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.65/1.85             ( l1_pre_topc @ B ) ) =>
% 1.65/1.85           ( ![C:$i]:
% 1.65/1.85             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.65/1.85               ( ![D:$i]:
% 1.65/1.85                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.65/1.85                   ( ![E:$i]:
% 1.65/1.85                     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.85                         ( v1_funct_2 @
% 1.65/1.85                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.85                         ( m1_subset_1 @
% 1.65/1.85                           E @ 
% 1.65/1.85                           ( k1_zfmisc_1 @
% 1.65/1.85                             ( k2_zfmisc_1 @
% 1.65/1.85                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.85                       ( ![F:$i]:
% 1.65/1.85                         ( ( ( v1_funct_1 @ F ) & 
% 1.65/1.85                             ( v1_funct_2 @
% 1.65/1.85                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.85                             ( m1_subset_1 @
% 1.65/1.85                               F @ 
% 1.65/1.85                               ( k1_zfmisc_1 @
% 1.65/1.85                                 ( k2_zfmisc_1 @
% 1.65/1.85                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.85                           ( ![G:$i]:
% 1.65/1.85                             ( ( ( v1_funct_1 @ G ) & 
% 1.65/1.85                                 ( v1_funct_2 @
% 1.65/1.85                                   G @ ( u1_struct_0 @ D ) @ 
% 1.65/1.85                                   ( u1_struct_0 @ B ) ) & 
% 1.65/1.85                                 ( m1_subset_1 @
% 1.65/1.85                                   G @ 
% 1.65/1.85                                   ( k1_zfmisc_1 @
% 1.65/1.85                                     ( k2_zfmisc_1 @
% 1.65/1.85                                       ( u1_struct_0 @ D ) @ 
% 1.65/1.85                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.85                               ( ( ( ( D ) = ( A ) ) & 
% 1.65/1.85                                   ( r1_funct_2 @
% 1.65/1.85                                     ( u1_struct_0 @ A ) @ 
% 1.65/1.85                                     ( u1_struct_0 @ B ) @ 
% 1.65/1.85                                     ( u1_struct_0 @ D ) @ 
% 1.65/1.85                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.65/1.85                                 ( ( r2_funct_2 @
% 1.65/1.85                                     ( u1_struct_0 @ C ) @ 
% 1.65/1.85                                     ( u1_struct_0 @ B ) @ 
% 1.65/1.85                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.65/1.85                                   ( r2_funct_2 @
% 1.65/1.85                                     ( u1_struct_0 @ C ) @ 
% 1.65/1.85                                     ( u1_struct_0 @ B ) @ 
% 1.65/1.85                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.65/1.85  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.85    (~( ![A:$i]:
% 1.65/1.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.65/1.85            ( l1_pre_topc @ A ) ) =>
% 1.65/1.85          ( ![B:$i]:
% 1.65/1.85            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.65/1.85                ( l1_pre_topc @ B ) ) =>
% 1.65/1.85              ( ![C:$i]:
% 1.65/1.85                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.65/1.85                  ( ![D:$i]:
% 1.65/1.85                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.65/1.85                      ( ![E:$i]:
% 1.65/1.85                        ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.85                            ( v1_funct_2 @
% 1.65/1.85                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.85                            ( m1_subset_1 @
% 1.65/1.85                              E @ 
% 1.65/1.85                              ( k1_zfmisc_1 @
% 1.65/1.85                                ( k2_zfmisc_1 @
% 1.65/1.85                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.85                          ( ![F:$i]:
% 1.65/1.85                            ( ( ( v1_funct_1 @ F ) & 
% 1.65/1.85                                ( v1_funct_2 @
% 1.65/1.85                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.85                                ( m1_subset_1 @
% 1.65/1.85                                  F @ 
% 1.65/1.85                                  ( k1_zfmisc_1 @
% 1.65/1.85                                    ( k2_zfmisc_1 @
% 1.65/1.85                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.85                              ( ![G:$i]:
% 1.65/1.85                                ( ( ( v1_funct_1 @ G ) & 
% 1.65/1.85                                    ( v1_funct_2 @
% 1.65/1.85                                      G @ ( u1_struct_0 @ D ) @ 
% 1.65/1.85                                      ( u1_struct_0 @ B ) ) & 
% 1.65/1.85                                    ( m1_subset_1 @
% 1.65/1.85                                      G @ 
% 1.65/1.85                                      ( k1_zfmisc_1 @
% 1.65/1.85                                        ( k2_zfmisc_1 @
% 1.65/1.85                                          ( u1_struct_0 @ D ) @ 
% 1.65/1.85                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.85                                  ( ( ( ( D ) = ( A ) ) & 
% 1.65/1.85                                      ( r1_funct_2 @
% 1.65/1.85                                        ( u1_struct_0 @ A ) @ 
% 1.65/1.85                                        ( u1_struct_0 @ B ) @ 
% 1.65/1.85                                        ( u1_struct_0 @ D ) @ 
% 1.65/1.85                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.65/1.85                                    ( ( r2_funct_2 @
% 1.65/1.85                                        ( u1_struct_0 @ C ) @ 
% 1.65/1.85                                        ( u1_struct_0 @ B ) @ 
% 1.65/1.85                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.65/1.85                                      ( r2_funct_2 @
% 1.65/1.85                                        ( u1_struct_0 @ C ) @ 
% 1.65/1.85                                        ( u1_struct_0 @ B ) @ 
% 1.65/1.85                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.65/1.85    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 1.65/1.85  thf('0', plain,
% 1.65/1.85      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)
% 1.65/1.85        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85             (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('1', plain,
% 1.65/1.85      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.65/1.85         <= (~
% 1.65/1.85             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('split', [status(esa)], ['0'])).
% 1.65/1.85  thf('2', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('3', plain,
% 1.65/1.85      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85           (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.65/1.85         <= (~
% 1.65/1.85             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('demod', [status(thm)], ['1', '2'])).
% 1.65/1.85  thf('4', plain,
% 1.65/1.85      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('5', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('6', plain,
% 1.65/1.85      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 1.65/1.85      inference('demod', [status(thm)], ['4', '5'])).
% 1.65/1.85  thf('7', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_E @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('8', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('9', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_E @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('demod', [status(thm)], ['7', '8'])).
% 1.65/1.85  thf(redefinition_r1_funct_2, axiom,
% 1.65/1.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.85     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 1.65/1.85         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 1.65/1.85         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.85         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 1.65/1.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.85       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 1.65/1.85  thf('10', plain,
% 1.65/1.85      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.65/1.85         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.65/1.85          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 1.65/1.85          | ~ (v1_funct_1 @ X24)
% 1.65/1.85          | (v1_xboole_0 @ X27)
% 1.65/1.85          | (v1_xboole_0 @ X26)
% 1.65/1.85          | ~ (v1_funct_1 @ X28)
% 1.65/1.85          | ~ (v1_funct_2 @ X28 @ X29 @ X27)
% 1.65/1.85          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 1.65/1.85          | ((X24) = (X28))
% 1.65/1.85          | ~ (r1_funct_2 @ X25 @ X26 @ X29 @ X27 @ X24 @ X28))),
% 1.65/1.85      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 1.65/1.85  thf('11', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.85         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 1.65/1.85             X1 @ sk_E @ X0)
% 1.65/1.85          | ((sk_E) = (X0))
% 1.65/1.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.85          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.65/1.85          | ~ (v1_funct_1 @ X0)
% 1.65/1.85          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | (v1_xboole_0 @ X1)
% 1.65/1.85          | ~ (v1_funct_1 @ sk_E)
% 1.65/1.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.65/1.85               (u1_struct_0 @ sk_B_1)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['9', '10'])).
% 1.65/1.85  thf('12', plain, ((v1_funct_1 @ sk_E)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('13', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('14', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('15', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('demod', [status(thm)], ['13', '14'])).
% 1.65/1.85  thf('16', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.85         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 1.65/1.85             X1 @ sk_E @ X0)
% 1.65/1.85          | ((sk_E) = (X0))
% 1.65/1.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.85          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.65/1.85          | ~ (v1_funct_1 @ X0)
% 1.65/1.85          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | (v1_xboole_0 @ X1))),
% 1.65/1.85      inference('demod', [status(thm)], ['11', '12', '15'])).
% 1.65/1.85  thf('17', plain,
% 1.65/1.85      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85        | ~ (v1_funct_1 @ sk_G)
% 1.65/1.85        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85        | ~ (m1_subset_1 @ sk_G @ 
% 1.65/1.85             (k1_zfmisc_1 @ 
% 1.65/1.85              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))
% 1.65/1.85        | ((sk_E) = (sk_G)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['6', '16'])).
% 1.65/1.85  thf('18', plain, ((v1_funct_1 @ sk_G)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('19', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('20', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_G @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('21', plain,
% 1.65/1.85      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85        | ((sk_E) = (sk_G)))),
% 1.65/1.85      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 1.65/1.85  thf('22', plain,
% 1.65/1.85      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.65/1.85      inference('simplify', [status(thm)], ['21'])).
% 1.65/1.85  thf('23', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_G @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf(cc4_relset_1, axiom,
% 1.65/1.85    (![A:$i,B:$i]:
% 1.65/1.85     ( ( v1_xboole_0 @ A ) =>
% 1.65/1.85       ( ![C:$i]:
% 1.65/1.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.65/1.85           ( v1_xboole_0 @ C ) ) ) ))).
% 1.65/1.85  thf('24', plain,
% 1.65/1.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.65/1.85         (~ (v1_xboole_0 @ X17)
% 1.65/1.85          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X17)))
% 1.65/1.85          | (v1_xboole_0 @ X18))),
% 1.65/1.85      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.65/1.85  thf('25', plain,
% 1.65/1.85      (((v1_xboole_0 @ sk_G) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['23', '24'])).
% 1.65/1.85  thf('26', plain, ((((sk_E) = (sk_G)) | (v1_xboole_0 @ sk_G))),
% 1.65/1.85      inference('sup-', [status(thm)], ['22', '25'])).
% 1.65/1.85  thf(d3_tarski, axiom,
% 1.65/1.85    (![A:$i,B:$i]:
% 1.65/1.85     ( ( r1_tarski @ A @ B ) <=>
% 1.65/1.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.65/1.85  thf('27', plain,
% 1.65/1.85      (![X4 : $i, X6 : $i]:
% 1.65/1.85         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.65/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.65/1.85  thf(d1_xboole_0, axiom,
% 1.65/1.85    (![A:$i]:
% 1.65/1.85     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.65/1.85  thf('28', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.65/1.85  thf('29', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.85      inference('sup-', [status(thm)], ['27', '28'])).
% 1.65/1.85  thf('30', plain, (![X0 : $i]: (((sk_E) = (sk_G)) | (r1_tarski @ sk_G @ X0))),
% 1.65/1.85      inference('sup-', [status(thm)], ['26', '29'])).
% 1.65/1.85  thf('31', plain,
% 1.65/1.85      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.65/1.85      inference('simplify', [status(thm)], ['21'])).
% 1.65/1.85  thf('32', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_E @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('demod', [status(thm)], ['7', '8'])).
% 1.65/1.85  thf('33', plain,
% 1.65/1.85      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.65/1.85         (~ (v1_xboole_0 @ X17)
% 1.65/1.85          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X17)))
% 1.65/1.85          | (v1_xboole_0 @ X18))),
% 1.65/1.85      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.65/1.85  thf('34', plain,
% 1.65/1.85      (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['32', '33'])).
% 1.65/1.85  thf('35', plain, ((((sk_E) = (sk_G)) | (v1_xboole_0 @ sk_E))),
% 1.65/1.85      inference('sup-', [status(thm)], ['31', '34'])).
% 1.65/1.85  thf('36', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.85      inference('sup-', [status(thm)], ['27', '28'])).
% 1.65/1.85  thf('37', plain, (![X0 : $i]: (((sk_E) = (sk_G)) | (r1_tarski @ sk_E @ X0))),
% 1.65/1.85      inference('sup-', [status(thm)], ['35', '36'])).
% 1.65/1.85  thf(d10_xboole_0, axiom,
% 1.65/1.85    (![A:$i,B:$i]:
% 1.65/1.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.65/1.85  thf('38', plain,
% 1.65/1.85      (![X7 : $i, X9 : $i]:
% 1.65/1.85         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.65/1.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.85  thf('39', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         (((sk_E) = (sk_G)) | ~ (r1_tarski @ X0 @ sk_E) | ((X0) = (sk_E)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['37', '38'])).
% 1.65/1.85  thf('40', plain,
% 1.65/1.85      ((((sk_E) = (sk_G)) | ((sk_G) = (sk_E)) | ((sk_E) = (sk_G)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['30', '39'])).
% 1.65/1.85  thf('41', plain, (((sk_E) = (sk_G))),
% 1.65/1.85      inference('simplify', [status(thm)], ['40'])).
% 1.65/1.85  thf('42', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('43', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('44', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['42', '43'])).
% 1.65/1.85  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('46', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['45', '46'])).
% 1.65/1.85  thf('48', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_E @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('demod', [status(thm)], ['7', '8'])).
% 1.65/1.85  thf(d5_tmap_1, axiom,
% 1.65/1.85    (![A:$i]:
% 1.65/1.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.65/1.85       ( ![B:$i]:
% 1.65/1.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.65/1.85             ( l1_pre_topc @ B ) ) =>
% 1.65/1.85           ( ![C:$i]:
% 1.65/1.85             ( ( m1_pre_topc @ C @ A ) =>
% 1.65/1.85               ( ![D:$i]:
% 1.65/1.85                 ( ( m1_pre_topc @ D @ A ) =>
% 1.65/1.85                   ( ![E:$i]:
% 1.65/1.85                     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.85                         ( v1_funct_2 @
% 1.65/1.85                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.85                         ( m1_subset_1 @
% 1.65/1.85                           E @ 
% 1.65/1.85                           ( k1_zfmisc_1 @
% 1.65/1.85                             ( k2_zfmisc_1 @
% 1.65/1.85                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.85                       ( ( m1_pre_topc @ D @ C ) =>
% 1.65/1.85                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.65/1.85                           ( k2_partfun1 @
% 1.65/1.85                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.65/1.85                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.65/1.85  thf('49', plain,
% 1.65/1.85      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.65/1.85         ((v2_struct_0 @ X34)
% 1.65/1.85          | ~ (v2_pre_topc @ X34)
% 1.65/1.85          | ~ (l1_pre_topc @ X34)
% 1.65/1.85          | ~ (m1_pre_topc @ X35 @ X36)
% 1.65/1.85          | ~ (m1_pre_topc @ X35 @ X37)
% 1.65/1.85          | ((k3_tmap_1 @ X36 @ X34 @ X37 @ X35 @ X38)
% 1.65/1.85              = (k2_partfun1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X34) @ 
% 1.65/1.85                 X38 @ (u1_struct_0 @ X35)))
% 1.65/1.85          | ~ (m1_subset_1 @ X38 @ 
% 1.65/1.85               (k1_zfmisc_1 @ 
% 1.65/1.85                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X34))))
% 1.65/1.85          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X34))
% 1.65/1.85          | ~ (v1_funct_1 @ X38)
% 1.65/1.85          | ~ (m1_pre_topc @ X37 @ X36)
% 1.65/1.85          | ~ (l1_pre_topc @ X36)
% 1.65/1.85          | ~ (v2_pre_topc @ X36)
% 1.65/1.85          | (v2_struct_0 @ X36))),
% 1.65/1.85      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.65/1.85  thf('50', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]:
% 1.65/1.85         ((v2_struct_0 @ X0)
% 1.65/1.85          | ~ (v2_pre_topc @ X0)
% 1.65/1.85          | ~ (l1_pre_topc @ X0)
% 1.65/1.85          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.65/1.85          | ~ (v1_funct_1 @ sk_E)
% 1.65/1.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.65/1.85               (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 1.65/1.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85                 sk_E @ (u1_struct_0 @ X1)))
% 1.65/1.85          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.65/1.85          | ~ (m1_pre_topc @ X1 @ X0)
% 1.65/1.85          | ~ (l1_pre_topc @ sk_B_1)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_B_1)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('sup-', [status(thm)], ['48', '49'])).
% 1.65/1.85  thf('51', plain, ((v1_funct_1 @ sk_E)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('52', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('demod', [status(thm)], ['13', '14'])).
% 1.65/1.85  thf('53', plain, ((l1_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('54', plain, ((v2_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('55', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]:
% 1.65/1.85         ((v2_struct_0 @ X0)
% 1.65/1.85          | ~ (v2_pre_topc @ X0)
% 1.65/1.85          | ~ (l1_pre_topc @ X0)
% 1.65/1.85          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.65/1.85          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 1.65/1.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85                 sk_E @ (u1_struct_0 @ X1)))
% 1.65/1.85          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.65/1.85          | ~ (m1_pre_topc @ X1 @ X0)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 1.65/1.85  thf('56', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         ((v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 1.65/1.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85                 sk_E @ (u1_struct_0 @ X0)))
% 1.65/1.85          | ~ (l1_pre_topc @ sk_D)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_D))),
% 1.65/1.85      inference('sup-', [status(thm)], ['47', '55'])).
% 1.65/1.85  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('58', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('59', plain, ((l1_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['57', '58'])).
% 1.65/1.85  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('61', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('62', plain, ((v2_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['60', '61'])).
% 1.65/1.85  thf('63', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         ((v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 1.65/1.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85                 sk_E @ (u1_struct_0 @ X0)))
% 1.65/1.85          | (v2_struct_0 @ sk_D))),
% 1.65/1.85      inference('demod', [status(thm)], ['56', '59', '62'])).
% 1.65/1.85  thf('64', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         ((v2_struct_0 @ sk_D)
% 1.65/1.85          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 1.65/1.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85                 sk_E @ (u1_struct_0 @ X0)))
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('simplify', [status(thm)], ['63'])).
% 1.65/1.85  thf('65', plain,
% 1.65/1.85      (((v2_struct_0 @ sk_B_1)
% 1.65/1.85        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 1.65/1.85            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               sk_E @ (u1_struct_0 @ sk_C_1)))
% 1.65/1.85        | (v2_struct_0 @ sk_D))),
% 1.65/1.85      inference('sup-', [status(thm)], ['44', '64'])).
% 1.65/1.85  thf('66', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('67', plain,
% 1.65/1.85      (((v2_struct_0 @ sk_D)
% 1.65/1.85        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 1.65/1.85            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 1.65/1.85      inference('clc', [status(thm)], ['65', '66'])).
% 1.65/1.85  thf('68', plain, (~ (v2_struct_0 @ sk_D)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('69', plain,
% 1.65/1.85      (((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 1.65/1.85         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 1.65/1.85      inference('clc', [status(thm)], ['67', '68'])).
% 1.65/1.85  thf('70', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['42', '43'])).
% 1.65/1.85  thf('71', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_E @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('demod', [status(thm)], ['7', '8'])).
% 1.65/1.85  thf(d4_tmap_1, axiom,
% 1.65/1.85    (![A:$i]:
% 1.65/1.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.65/1.85       ( ![B:$i]:
% 1.65/1.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.65/1.85             ( l1_pre_topc @ B ) ) =>
% 1.65/1.85           ( ![C:$i]:
% 1.65/1.85             ( ( ( v1_funct_1 @ C ) & 
% 1.65/1.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.85                 ( m1_subset_1 @
% 1.65/1.85                   C @ 
% 1.65/1.85                   ( k1_zfmisc_1 @
% 1.65/1.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.85               ( ![D:$i]:
% 1.65/1.85                 ( ( m1_pre_topc @ D @ A ) =>
% 1.65/1.85                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.65/1.85                     ( k2_partfun1 @
% 1.65/1.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.65/1.85                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.65/1.85  thf('72', plain,
% 1.65/1.85      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.65/1.85         ((v2_struct_0 @ X30)
% 1.65/1.85          | ~ (v2_pre_topc @ X30)
% 1.65/1.85          | ~ (l1_pre_topc @ X30)
% 1.65/1.85          | ~ (m1_pre_topc @ X31 @ X32)
% 1.65/1.85          | ((k2_tmap_1 @ X32 @ X30 @ X33 @ X31)
% 1.65/1.85              = (k2_partfun1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 1.65/1.85                 X33 @ (u1_struct_0 @ X31)))
% 1.65/1.85          | ~ (m1_subset_1 @ X33 @ 
% 1.65/1.85               (k1_zfmisc_1 @ 
% 1.65/1.85                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 1.65/1.85          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 1.65/1.85          | ~ (v1_funct_1 @ X33)
% 1.65/1.85          | ~ (l1_pre_topc @ X32)
% 1.65/1.85          | ~ (v2_pre_topc @ X32)
% 1.65/1.85          | (v2_struct_0 @ X32))),
% 1.65/1.85      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.65/1.85  thf('73', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         ((v2_struct_0 @ sk_D)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_D)
% 1.65/1.85          | ~ (l1_pre_topc @ sk_D)
% 1.65/1.85          | ~ (v1_funct_1 @ sk_E)
% 1.65/1.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.65/1.85               (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 1.65/1.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85                 sk_E @ (u1_struct_0 @ X0)))
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | ~ (l1_pre_topc @ sk_B_1)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_B_1)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('sup-', [status(thm)], ['71', '72'])).
% 1.65/1.85  thf('74', plain, ((v2_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['60', '61'])).
% 1.65/1.85  thf('75', plain, ((l1_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['57', '58'])).
% 1.65/1.85  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('77', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('demod', [status(thm)], ['13', '14'])).
% 1.65/1.85  thf('78', plain, ((l1_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('79', plain, ((v2_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('80', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         ((v2_struct_0 @ sk_D)
% 1.65/1.85          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 1.65/1.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85                 sk_E @ (u1_struct_0 @ X0)))
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('demod', [status(thm)],
% 1.65/1.85                ['73', '74', '75', '76', '77', '78', '79'])).
% 1.65/1.85  thf('81', plain,
% 1.65/1.85      (((v2_struct_0 @ sk_B_1)
% 1.65/1.85        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.65/1.85            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               sk_E @ (u1_struct_0 @ sk_C_1)))
% 1.65/1.85        | (v2_struct_0 @ sk_D))),
% 1.65/1.85      inference('sup-', [status(thm)], ['70', '80'])).
% 1.65/1.85  thf('82', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('83', plain,
% 1.65/1.85      (((v2_struct_0 @ sk_D)
% 1.65/1.85        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.65/1.85            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 1.65/1.85      inference('clc', [status(thm)], ['81', '82'])).
% 1.65/1.85  thf('84', plain, (~ (v2_struct_0 @ sk_D)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('85', plain,
% 1.65/1.85      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.65/1.85         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 1.65/1.85      inference('clc', [status(thm)], ['83', '84'])).
% 1.65/1.85  thf('86', plain,
% 1.65/1.85      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.65/1.85         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))),
% 1.65/1.85      inference('sup+', [status(thm)], ['69', '85'])).
% 1.65/1.85  thf('87', plain,
% 1.65/1.85      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.65/1.85         <= (~
% 1.65/1.85             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('demod', [status(thm)], ['3', '41', '86'])).
% 1.65/1.85  thf('88', plain,
% 1.65/1.85      (~
% 1.65/1.85       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 1.65/1.85       ~
% 1.65/1.85       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 1.65/1.85      inference('split', [status(esa)], ['0'])).
% 1.65/1.85  thf('89', plain,
% 1.65/1.85      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.65/1.85         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))),
% 1.65/1.85      inference('sup+', [status(thm)], ['69', '85'])).
% 1.65/1.85  thf('90', plain, (((sk_E) = (sk_G))),
% 1.65/1.85      inference('simplify', [status(thm)], ['40'])).
% 1.65/1.85  thf('91', plain,
% 1.65/1.85      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)
% 1.65/1.85        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('92', plain,
% 1.65/1.85      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.65/1.85         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('split', [status(esa)], ['91'])).
% 1.65/1.85  thf('93', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('94', plain,
% 1.65/1.85      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.65/1.85         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.85  thf('95', plain,
% 1.65/1.85      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 1.65/1.85         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('sup+', [status(thm)], ['90', '94'])).
% 1.65/1.85  thf('96', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['42', '43'])).
% 1.65/1.85  thf('97', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['45', '46'])).
% 1.65/1.85  thf('98', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_E @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('demod', [status(thm)], ['7', '8'])).
% 1.65/1.85  thf(dt_k3_tmap_1, axiom,
% 1.65/1.85    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.65/1.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.65/1.85         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.65/1.85         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.65/1.85         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.65/1.85         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.85         ( m1_subset_1 @
% 1.65/1.85           E @ 
% 1.65/1.85           ( k1_zfmisc_1 @
% 1.65/1.85             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.85       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.65/1.85         ( v1_funct_2 @
% 1.65/1.85           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.65/1.85           ( u1_struct_0 @ B ) ) & 
% 1.65/1.85         ( m1_subset_1 @
% 1.65/1.85           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.65/1.85           ( k1_zfmisc_1 @
% 1.65/1.85             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.65/1.85  thf('99', plain,
% 1.65/1.85      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.65/1.85         (~ (m1_pre_topc @ X39 @ X40)
% 1.65/1.85          | ~ (m1_pre_topc @ X41 @ X40)
% 1.65/1.85          | ~ (l1_pre_topc @ X42)
% 1.65/1.85          | ~ (v2_pre_topc @ X42)
% 1.65/1.85          | (v2_struct_0 @ X42)
% 1.65/1.85          | ~ (l1_pre_topc @ X40)
% 1.65/1.85          | ~ (v2_pre_topc @ X40)
% 1.65/1.85          | (v2_struct_0 @ X40)
% 1.65/1.85          | ~ (v1_funct_1 @ X43)
% 1.65/1.85          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X42))
% 1.65/1.85          | ~ (m1_subset_1 @ X43 @ 
% 1.65/1.85               (k1_zfmisc_1 @ 
% 1.65/1.85                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X42))))
% 1.65/1.85          | (m1_subset_1 @ (k3_tmap_1 @ X40 @ X42 @ X41 @ X39 @ X43) @ 
% 1.65/1.85             (k1_zfmisc_1 @ 
% 1.65/1.85              (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42)))))),
% 1.65/1.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.65/1.85  thf('100', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]:
% 1.65/1.85         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 1.65/1.85           (k1_zfmisc_1 @ 
% 1.65/1.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 1.65/1.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.65/1.85               (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | ~ (v1_funct_1 @ sk_E)
% 1.65/1.85          | (v2_struct_0 @ X1)
% 1.65/1.85          | ~ (v2_pre_topc @ X1)
% 1.65/1.85          | ~ (l1_pre_topc @ X1)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_B_1)
% 1.65/1.85          | ~ (l1_pre_topc @ sk_B_1)
% 1.65/1.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.65/1.85      inference('sup-', [status(thm)], ['98', '99'])).
% 1.65/1.85  thf('101', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('demod', [status(thm)], ['13', '14'])).
% 1.65/1.85  thf('102', plain, ((v1_funct_1 @ sk_E)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('103', plain, ((v2_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('104', plain, ((l1_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('105', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]:
% 1.65/1.85         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 1.65/1.85           (k1_zfmisc_1 @ 
% 1.65/1.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 1.65/1.85          | (v2_struct_0 @ X1)
% 1.65/1.85          | ~ (v2_pre_topc @ X1)
% 1.65/1.85          | ~ (l1_pre_topc @ X1)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.65/1.85      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 1.65/1.85  thf('106', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (l1_pre_topc @ sk_D)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_D)
% 1.65/1.85          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 1.65/1.85             (k1_zfmisc_1 @ 
% 1.65/1.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))))),
% 1.65/1.85      inference('sup-', [status(thm)], ['97', '105'])).
% 1.65/1.85  thf('107', plain, ((l1_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['57', '58'])).
% 1.65/1.85  thf('108', plain, ((v2_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['60', '61'])).
% 1.65/1.85  thf('109', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | (v2_struct_0 @ sk_D)
% 1.65/1.85          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 1.65/1.85             (k1_zfmisc_1 @ 
% 1.65/1.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))))),
% 1.65/1.85      inference('demod', [status(thm)], ['106', '107', '108'])).
% 1.65/1.85  thf('110', plain,
% 1.65/1.85      (((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ 
% 1.65/1.85         (k1_zfmisc_1 @ 
% 1.65/1.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))
% 1.65/1.85        | (v2_struct_0 @ sk_D)
% 1.65/1.85        | (v2_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('sup-', [status(thm)], ['96', '109'])).
% 1.65/1.85  thf('111', plain, (~ (v2_struct_0 @ sk_D)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('112', plain,
% 1.65/1.85      (((v2_struct_0 @ sk_B_1)
% 1.65/1.85        | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ 
% 1.65/1.85           (k1_zfmisc_1 @ 
% 1.65/1.85            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1)))))),
% 1.65/1.85      inference('clc', [status(thm)], ['110', '111'])).
% 1.65/1.85  thf('113', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('114', plain,
% 1.65/1.85      ((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('clc', [status(thm)], ['112', '113'])).
% 1.65/1.85  thf(redefinition_r2_funct_2, axiom,
% 1.65/1.85    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.85         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.65/1.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.85       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.65/1.85  thf('115', plain,
% 1.65/1.85      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.65/1.85         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.65/1.85          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 1.65/1.85          | ~ (v1_funct_1 @ X20)
% 1.65/1.85          | ~ (v1_funct_1 @ X23)
% 1.65/1.85          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 1.65/1.85          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.65/1.85          | ((X20) = (X23))
% 1.65/1.85          | ~ (r2_funct_2 @ X21 @ X22 @ X20 @ X23))),
% 1.65/1.85      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.65/1.85  thf('116', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85             (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ X0)
% 1.65/1.85          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) = (X0))
% 1.65/1.85          | ~ (m1_subset_1 @ X0 @ 
% 1.65/1.85               (k1_zfmisc_1 @ 
% 1.65/1.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))
% 1.65/1.85          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C_1) @ 
% 1.65/1.85               (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | ~ (v1_funct_1 @ X0)
% 1.65/1.85          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))
% 1.65/1.85          | ~ (v1_funct_2 @ 
% 1.65/1.85               (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ 
% 1.65/1.85               (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['114', '115'])).
% 1.65/1.85  thf('117', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['42', '43'])).
% 1.65/1.85  thf('118', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['45', '46'])).
% 1.65/1.85  thf('119', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_E @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('demod', [status(thm)], ['7', '8'])).
% 1.65/1.85  thf('120', plain,
% 1.65/1.85      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.65/1.85         (~ (m1_pre_topc @ X39 @ X40)
% 1.65/1.85          | ~ (m1_pre_topc @ X41 @ X40)
% 1.65/1.85          | ~ (l1_pre_topc @ X42)
% 1.65/1.85          | ~ (v2_pre_topc @ X42)
% 1.65/1.85          | (v2_struct_0 @ X42)
% 1.65/1.85          | ~ (l1_pre_topc @ X40)
% 1.65/1.85          | ~ (v2_pre_topc @ X40)
% 1.65/1.85          | (v2_struct_0 @ X40)
% 1.65/1.85          | ~ (v1_funct_1 @ X43)
% 1.65/1.85          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X42))
% 1.65/1.85          | ~ (m1_subset_1 @ X43 @ 
% 1.65/1.85               (k1_zfmisc_1 @ 
% 1.65/1.85                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X42))))
% 1.65/1.85          | (v1_funct_1 @ (k3_tmap_1 @ X40 @ X42 @ X41 @ X39 @ X43)))),
% 1.65/1.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.65/1.85  thf('121', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]:
% 1.65/1.85         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E))
% 1.65/1.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.65/1.85               (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | ~ (v1_funct_1 @ sk_E)
% 1.65/1.85          | (v2_struct_0 @ X1)
% 1.65/1.85          | ~ (v2_pre_topc @ X1)
% 1.65/1.85          | ~ (l1_pre_topc @ X1)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_B_1)
% 1.65/1.85          | ~ (l1_pre_topc @ sk_B_1)
% 1.65/1.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.65/1.85      inference('sup-', [status(thm)], ['119', '120'])).
% 1.65/1.85  thf('122', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('demod', [status(thm)], ['13', '14'])).
% 1.65/1.85  thf('123', plain, ((v1_funct_1 @ sk_E)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('124', plain, ((v2_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('125', plain, ((l1_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('126', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]:
% 1.65/1.85         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E))
% 1.65/1.85          | (v2_struct_0 @ X1)
% 1.65/1.85          | ~ (v2_pre_topc @ X1)
% 1.65/1.85          | ~ (l1_pre_topc @ X1)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.65/1.85      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 1.65/1.85  thf('127', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (l1_pre_topc @ sk_D)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_D)
% 1.65/1.85          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['118', '126'])).
% 1.65/1.85  thf('128', plain, ((l1_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['57', '58'])).
% 1.65/1.85  thf('129', plain, ((v2_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['60', '61'])).
% 1.65/1.85  thf('130', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | (v2_struct_0 @ sk_D)
% 1.65/1.85          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)))),
% 1.65/1.85      inference('demod', [status(thm)], ['127', '128', '129'])).
% 1.65/1.85  thf('131', plain,
% 1.65/1.85      (((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))
% 1.65/1.85        | (v2_struct_0 @ sk_D)
% 1.65/1.85        | (v2_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('sup-', [status(thm)], ['117', '130'])).
% 1.65/1.85  thf('132', plain, (~ (v2_struct_0 @ sk_D)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('133', plain,
% 1.65/1.85      (((v2_struct_0 @ sk_B_1)
% 1.65/1.85        | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)))),
% 1.65/1.85      inference('clc', [status(thm)], ['131', '132'])).
% 1.65/1.85  thf('134', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('135', plain,
% 1.65/1.85      ((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))),
% 1.65/1.85      inference('clc', [status(thm)], ['133', '134'])).
% 1.65/1.85  thf('136', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['42', '43'])).
% 1.65/1.85  thf('137', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['45', '46'])).
% 1.65/1.85  thf('138', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_E @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('demod', [status(thm)], ['7', '8'])).
% 1.65/1.85  thf('139', plain,
% 1.65/1.85      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.65/1.85         (~ (m1_pre_topc @ X39 @ X40)
% 1.65/1.85          | ~ (m1_pre_topc @ X41 @ X40)
% 1.65/1.85          | ~ (l1_pre_topc @ X42)
% 1.65/1.85          | ~ (v2_pre_topc @ X42)
% 1.65/1.85          | (v2_struct_0 @ X42)
% 1.65/1.85          | ~ (l1_pre_topc @ X40)
% 1.65/1.85          | ~ (v2_pre_topc @ X40)
% 1.65/1.85          | (v2_struct_0 @ X40)
% 1.65/1.85          | ~ (v1_funct_1 @ X43)
% 1.65/1.85          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X42))
% 1.65/1.85          | ~ (m1_subset_1 @ X43 @ 
% 1.65/1.85               (k1_zfmisc_1 @ 
% 1.65/1.85                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X42))))
% 1.65/1.85          | (v1_funct_2 @ (k3_tmap_1 @ X40 @ X42 @ X41 @ X39 @ X43) @ 
% 1.65/1.85             (u1_struct_0 @ X39) @ (u1_struct_0 @ X42)))),
% 1.65/1.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.65/1.85  thf('140', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]:
% 1.65/1.85         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 1.65/1.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.65/1.85               (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | ~ (v1_funct_1 @ sk_E)
% 1.65/1.85          | (v2_struct_0 @ X1)
% 1.65/1.85          | ~ (v2_pre_topc @ X1)
% 1.65/1.85          | ~ (l1_pre_topc @ X1)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_B_1)
% 1.65/1.85          | ~ (l1_pre_topc @ sk_B_1)
% 1.65/1.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.65/1.85      inference('sup-', [status(thm)], ['138', '139'])).
% 1.65/1.85  thf('141', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('demod', [status(thm)], ['13', '14'])).
% 1.65/1.85  thf('142', plain, ((v1_funct_1 @ sk_E)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('143', plain, ((v2_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('144', plain, ((l1_pre_topc @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('145', plain,
% 1.65/1.85      (![X0 : $i, X1 : $i]:
% 1.65/1.85         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 1.65/1.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | (v2_struct_0 @ X1)
% 1.65/1.85          | ~ (v2_pre_topc @ X1)
% 1.65/1.85          | ~ (l1_pre_topc @ X1)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.65/1.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.65/1.85      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 1.65/1.85  thf('146', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | ~ (l1_pre_topc @ sk_D)
% 1.65/1.85          | ~ (v2_pre_topc @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_D)
% 1.65/1.85          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 1.65/1.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['137', '145'])).
% 1.65/1.85  thf('147', plain, ((l1_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['57', '58'])).
% 1.65/1.85  thf('148', plain, ((v2_pre_topc @ sk_D)),
% 1.65/1.85      inference('demod', [status(thm)], ['60', '61'])).
% 1.65/1.85  thf('149', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.65/1.85          | (v2_struct_0 @ sk_B_1)
% 1.65/1.85          | (v2_struct_0 @ sk_D)
% 1.65/1.85          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 1.65/1.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))),
% 1.65/1.85      inference('demod', [status(thm)], ['146', '147', '148'])).
% 1.65/1.85  thf('150', plain,
% 1.65/1.85      (((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ 
% 1.65/1.85         (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85        | (v2_struct_0 @ sk_D)
% 1.65/1.85        | (v2_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('sup-', [status(thm)], ['136', '149'])).
% 1.65/1.85  thf('151', plain, (~ (v2_struct_0 @ sk_D)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('152', plain,
% 1.65/1.85      (((v2_struct_0 @ sk_B_1)
% 1.65/1.85        | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ 
% 1.65/1.85           (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1)))),
% 1.65/1.85      inference('clc', [status(thm)], ['150', '151'])).
% 1.65/1.85  thf('153', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('154', plain,
% 1.65/1.85      ((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ 
% 1.65/1.85        (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('clc', [status(thm)], ['152', '153'])).
% 1.65/1.85  thf('155', plain,
% 1.65/1.85      (![X0 : $i]:
% 1.65/1.85         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85             (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ X0)
% 1.65/1.85          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) = (X0))
% 1.65/1.85          | ~ (m1_subset_1 @ X0 @ 
% 1.65/1.85               (k1_zfmisc_1 @ 
% 1.65/1.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))
% 1.65/1.85          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C_1) @ 
% 1.65/1.85               (u1_struct_0 @ sk_B_1))
% 1.65/1.85          | ~ (v1_funct_1 @ X0))),
% 1.65/1.85      inference('demod', [status(thm)], ['116', '135', '154'])).
% 1.65/1.85  thf('156', plain,
% 1.65/1.85      (((~ (v1_funct_1 @ sk_F)
% 1.65/1.85         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C_1) @ 
% 1.65/1.85              (u1_struct_0 @ sk_B_1))
% 1.65/1.85         | ~ (m1_subset_1 @ sk_F @ 
% 1.65/1.85              (k1_zfmisc_1 @ 
% 1.65/1.85               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))
% 1.65/1.85         | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) = (sk_F))))
% 1.65/1.85         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['95', '155'])).
% 1.65/1.85  thf('157', plain, ((v1_funct_1 @ sk_F)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('158', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('159', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_F @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('160', plain,
% 1.65/1.85      ((((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) = (sk_F)))
% 1.65/1.85         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 1.65/1.85  thf('161', plain,
% 1.65/1.85      ((((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) = (sk_F)))
% 1.65/1.85         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('sup+', [status(thm)], ['89', '160'])).
% 1.65/1.85  thf('162', plain,
% 1.65/1.85      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.65/1.85         <= (~
% 1.65/1.85             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 1.65/1.85      inference('split', [status(esa)], ['0'])).
% 1.65/1.85  thf('163', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('164', plain,
% 1.65/1.85      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.65/1.85         <= (~
% 1.65/1.85             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 1.65/1.85      inference('demod', [status(thm)], ['162', '163'])).
% 1.65/1.85  thf('165', plain,
% 1.65/1.85      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85           sk_F @ sk_F))
% 1.65/1.85         <= (~
% 1.65/1.85             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)) & 
% 1.65/1.85             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.65/1.85      inference('sup-', [status(thm)], ['161', '164'])).
% 1.65/1.85  thf('166', plain,
% 1.65/1.85      ((m1_subset_1 @ sk_F @ 
% 1.65/1.85        (k1_zfmisc_1 @ 
% 1.65/1.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('167', plain,
% 1.65/1.85      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.65/1.85         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.65/1.85          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 1.65/1.85          | ~ (v1_funct_1 @ X20)
% 1.65/1.85          | ~ (v1_funct_1 @ X23)
% 1.65/1.85          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 1.65/1.85          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.65/1.85          | (r2_funct_2 @ X21 @ X22 @ X20 @ X23)
% 1.65/1.85          | ((X20) != (X23)))),
% 1.65/1.85      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.65/1.85  thf('168', plain,
% 1.65/1.85      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.65/1.85         ((r2_funct_2 @ X21 @ X22 @ X23 @ X23)
% 1.65/1.85          | ~ (v1_funct_1 @ X23)
% 1.65/1.85          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 1.65/1.85          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.65/1.85      inference('simplify', [status(thm)], ['167'])).
% 1.65/1.85  thf('169', plain,
% 1.65/1.85      ((~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))
% 1.65/1.85        | ~ (v1_funct_1 @ sk_F)
% 1.65/1.85        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85           sk_F @ sk_F))),
% 1.65/1.85      inference('sup-', [status(thm)], ['166', '168'])).
% 1.65/1.85  thf('170', plain,
% 1.65/1.85      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('171', plain, ((v1_funct_1 @ sk_F)),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('172', plain,
% 1.65/1.85      ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_F @ 
% 1.65/1.85        sk_F)),
% 1.65/1.85      inference('demod', [status(thm)], ['169', '170', '171'])).
% 1.65/1.85  thf('173', plain,
% 1.65/1.85      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)) | 
% 1.65/1.85       ~
% 1.65/1.85       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.65/1.85      inference('demod', [status(thm)], ['165', '172'])).
% 1.65/1.85  thf('174', plain,
% 1.65/1.85      (~
% 1.65/1.85       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.65/1.85      inference('sat_resolution*', [status(thm)], ['88', '173'])).
% 1.65/1.85  thf('175', plain,
% 1.65/1.85      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85          (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)),
% 1.65/1.85      inference('simpl_trail', [status(thm)], ['87', '174'])).
% 1.65/1.85  thf('176', plain,
% 1.65/1.85      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.65/1.85         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 1.65/1.85      inference('split', [status(esa)], ['91'])).
% 1.65/1.85  thf('177', plain, (((sk_D) = (sk_A))),
% 1.65/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.85  thf('178', plain,
% 1.65/1.85      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.65/1.85         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 1.65/1.85      inference('demod', [status(thm)], ['176', '177'])).
% 1.65/1.85  thf('179', plain,
% 1.65/1.85      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)) | 
% 1.65/1.85       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.65/1.85      inference('split', [status(esa)], ['91'])).
% 1.65/1.85  thf('180', plain,
% 1.65/1.85      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 1.65/1.85      inference('sat_resolution*', [status(thm)], ['88', '173', '179'])).
% 1.65/1.85  thf('181', plain,
% 1.65/1.85      ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.65/1.85        (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)),
% 1.65/1.85      inference('simpl_trail', [status(thm)], ['178', '180'])).
% 1.65/1.85  thf('182', plain, ($false), inference('demod', [status(thm)], ['175', '181'])).
% 1.65/1.85  
% 1.65/1.85  % SZS output end Refutation
% 1.65/1.85  
% 1.65/1.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
