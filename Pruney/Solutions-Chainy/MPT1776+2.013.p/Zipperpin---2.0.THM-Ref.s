%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tbT8dRnY7m

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:25 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 503 expanded)
%              Number of leaves         :   34 ( 153 expanded)
%              Depth                    :   33
%              Number of atoms          : 2008 (18583 expanded)
%              Number of equality atoms :   13 ( 233 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

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

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X14 ) )
      | ( v1_tsep_1 @ X12 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v1_tsep_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('48',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['51','52'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('54',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['5'])).

thf('58',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( v1_tsep_1 @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X28 ) )
      | ( X31 != X32 )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('62',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X32 )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( v1_tsep_1 @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('74',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74','75','76'])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['56','77'])).

thf('79',plain,
    ( ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['9'])).

thf('91',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference('sat_resolution*',[status(thm)],['15','19','89','90'])).

thf('92',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference(simpl_trail,[status(thm)],['6','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( F = G )
                                  & ( m1_pre_topc @ D @ C )
                                  & ( r1_tmap_1 @ C @ B @ E @ F ) )
                               => ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ G ) ) ) ) ) ) ) ) ) )).

thf('94',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X21 @ X24 )
      | ~ ( r1_tmap_1 @ X24 @ X20 @ X25 @ X23 )
      | ( X23 != X26 )
      | ( r1_tmap_1 @ X21 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25 ) @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('95',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X21 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25 ) @ X26 )
      | ~ ( r1_tmap_1 @ X24 @ X20 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X21 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('114',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('115',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('116',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['15','19','89','116'])).

thf('118',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['113','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['0','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tbT8dRnY7m
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 140 iterations in 0.091s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.36/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.55  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(t87_tmap_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55             ( l1_pre_topc @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.55                   ( ![E:$i]:
% 0.36/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.55                         ( v1_funct_2 @
% 0.36/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                         ( m1_subset_1 @
% 0.36/0.55                           E @ 
% 0.36/0.55                           ( k1_zfmisc_1 @
% 0.36/0.55                             ( k2_zfmisc_1 @
% 0.36/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.36/0.55                           ( m1_pre_topc @ C @ D ) ) =>
% 0.36/0.55                         ( ![F:$i]:
% 0.36/0.55                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.55                             ( ![G:$i]:
% 0.36/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.55                                 ( ( ( F ) = ( G ) ) =>
% 0.36/0.55                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.36/0.55                                     ( r1_tmap_1 @
% 0.36/0.55                                       C @ A @ 
% 0.36/0.55                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55            ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55                ( l1_pre_topc @ B ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.36/0.55                  ( ![D:$i]:
% 0.36/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.55                      ( ![E:$i]:
% 0.36/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.55                            ( v1_funct_2 @
% 0.36/0.55                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                            ( m1_subset_1 @
% 0.36/0.55                              E @ 
% 0.36/0.55                              ( k1_zfmisc_1 @
% 0.36/0.55                                ( k2_zfmisc_1 @
% 0.36/0.55                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.36/0.55                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.36/0.55                            ( ![F:$i]:
% 0.36/0.55                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.55                                ( ![G:$i]:
% 0.36/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.55                                    ( ( ( F ) = ( G ) ) =>
% 0.36/0.55                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.36/0.55                                        ( r1_tmap_1 @
% 0.36/0.55                                          C @ A @ 
% 0.36/0.55                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.36/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('3', plain, (((sk_F) = (sk_G))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.36/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.55      inference('split', [status(esa)], ['5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.36/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('8', plain, (((sk_F) = (sk_G))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.36/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)))),
% 0.36/0.55      inference('split', [status(esa)], ['9'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.36/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.55      inference('split', [status(esa)], ['11'])).
% 0.36/0.55  thf('13', plain, (((sk_F) = (sk_G))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (~
% 0.36/0.55       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)) | 
% 0.36/0.55       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.36/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('17', plain, (((sk_F) = (sk_G))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.36/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (~
% 0.36/0.55       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)) | 
% 0.36/0.55       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.55      inference('split', [status(esa)], ['18'])).
% 0.36/0.55  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('21', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t1_tsep_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.55           ( m1_subset_1 @
% 0.36/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X15 @ X16)
% 0.36/0.55          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.55          | ~ (l1_pre_topc @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_D)
% 0.36/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_m1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X9 @ X10)
% 0.36/0.55          | (l1_pre_topc @ X9)
% 0.36/0.55          | ~ (l1_pre_topc @ X10))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.55  thf('26', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.55  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('28', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['23', '28'])).
% 0.36/0.55  thf(d2_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.36/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.36/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X5 : $i, X6 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X5 @ X6)
% 0.36/0.55          | (r2_hidden @ X5 @ X6)
% 0.36/0.55          | (v1_xboole_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.36/0.55        | (r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf(d1_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.36/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X3 @ X2)
% 0.36/0.55          | (r1_tarski @ X3 @ X1)
% 0.36/0.55          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X1 : $i, X3 : $i]:
% 0.36/0.55         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.36/0.55        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['31', '33'])).
% 0.36/0.55  thf(t19_tsep_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.55               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.55                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.55         (~ (v1_tsep_1 @ X12 @ X13)
% 0.36/0.55          | ~ (m1_pre_topc @ X12 @ X13)
% 0.36/0.55          | ~ (r1_tarski @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X14))
% 0.36/0.55          | (v1_tsep_1 @ X12 @ X14)
% 0.36/0.55          | ~ (m1_pre_topc @ X14 @ X13)
% 0.36/0.55          | (v2_struct_0 @ X14)
% 0.36/0.55          | ~ (l1_pre_topc @ X13)
% 0.36/0.55          | ~ (v2_pre_topc @ X13)
% 0.36/0.55          | (v2_struct_0 @ X13))),
% 0.36/0.55      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | (v2_struct_0 @ sk_D)
% 0.36/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.55          | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.55          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.36/0.55          | ~ (v1_tsep_1 @ sk_C_1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      ((~ (v1_tsep_1 @ sk_C_1 @ sk_B)
% 0.36/0.55        | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.36/0.55        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '36'])).
% 0.36/0.55  thf('38', plain, ((v1_tsep_1 @ sk_C_1 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('39', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.36/0.55      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['23', '28'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X7 @ X6) | (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['42', '45'])).
% 0.36/0.55  thf(fc2_struct_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (![X11 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X11))
% 0.36/0.55          | ~ (l1_struct_0 @ X11)
% 0.36/0.55          | (v2_struct_0 @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1)
% 0.36/0.55        | ~ (l1_struct_0 @ sk_C_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.55  thf('49', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X9 @ X10)
% 0.36/0.55          | (l1_pre_topc @ X9)
% 0.36/0.55          | ~ (l1_pre_topc @ X10))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.55  thf('51', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.55  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('53', plain, ((l1_pre_topc @ sk_C_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.36/0.55  thf(dt_l1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.55  thf('54', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('55', plain, ((l1_struct_0 @ sk_C_1)),
% 0.36/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['48', '55'])).
% 0.36/0.55  thf('57', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.55      inference('split', [status(esa)], ['5'])).
% 0.36/0.55  thf('58', plain, (((sk_F) = (sk_G))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.55      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t86_tmap_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55             ( l1_pre_topc @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.55                   ( ![E:$i]:
% 0.36/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.55                         ( v1_funct_2 @
% 0.36/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.55                         ( m1_subset_1 @
% 0.36/0.55                           E @ 
% 0.36/0.55                           ( k1_zfmisc_1 @
% 0.36/0.55                             ( k2_zfmisc_1 @
% 0.36/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.55                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.36/0.55                         ( ![F:$i]:
% 0.36/0.55                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.55                             ( ![G:$i]:
% 0.36/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.55                                 ( ( ( F ) = ( G ) ) =>
% 0.36/0.55                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.36/0.55                                     ( r1_tmap_1 @
% 0.36/0.55                                       C @ B @ 
% 0.36/0.55                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('61', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X27)
% 0.36/0.55          | ~ (v2_pre_topc @ X27)
% 0.36/0.55          | ~ (l1_pre_topc @ X27)
% 0.36/0.55          | (v2_struct_0 @ X28)
% 0.36/0.55          | ~ (m1_pre_topc @ X28 @ X29)
% 0.36/0.55          | ~ (v1_tsep_1 @ X30 @ X28)
% 0.36/0.55          | ~ (m1_pre_topc @ X30 @ X28)
% 0.36/0.55          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X28))
% 0.36/0.55          | ((X31) != (X32))
% 0.36/0.55          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.36/0.55               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.36/0.55          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X31)
% 0.36/0.55          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.36/0.55          | ~ (m1_subset_1 @ X33 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.36/0.55          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.36/0.55          | ~ (v1_funct_1 @ X33)
% 0.36/0.55          | ~ (m1_pre_topc @ X30 @ X29)
% 0.36/0.56          | (v2_struct_0 @ X30)
% 0.36/0.56          | ~ (l1_pre_topc @ X29)
% 0.36/0.56          | ~ (v2_pre_topc @ X29)
% 0.36/0.56          | (v2_struct_0 @ X29))),
% 0.36/0.56      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X32 : $i, X33 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X29)
% 0.36/0.56          | ~ (v2_pre_topc @ X29)
% 0.36/0.56          | ~ (l1_pre_topc @ X29)
% 0.36/0.56          | (v2_struct_0 @ X30)
% 0.36/0.56          | ~ (m1_pre_topc @ X30 @ X29)
% 0.36/0.56          | ~ (v1_funct_1 @ X33)
% 0.36/0.56          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.36/0.56          | ~ (m1_subset_1 @ X33 @ 
% 0.36/0.56               (k1_zfmisc_1 @ 
% 0.36/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.36/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.36/0.56          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X32)
% 0.36/0.56          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.36/0.56               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.36/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.36/0.56          | ~ (m1_pre_topc @ X30 @ X28)
% 0.36/0.56          | ~ (v1_tsep_1 @ X30 @ X28)
% 0.36/0.56          | ~ (m1_pre_topc @ X28 @ X29)
% 0.36/0.56          | (v2_struct_0 @ X28)
% 0.36/0.56          | ~ (l1_pre_topc @ X27)
% 0.36/0.56          | ~ (v2_pre_topc @ X27)
% 0.36/0.56          | (v2_struct_0 @ X27))),
% 0.36/0.56      inference('simplify', [status(thm)], ['61'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ sk_D)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.56          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.36/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.36/0.56          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.36/0.56          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.36/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.36/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0)
% 0.36/0.56          | (v2_struct_0 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['60', '62'])).
% 0.36/0.56  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('66', plain,
% 0.36/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('67', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('68', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ sk_D)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.56          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.36/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.36/0.56          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.36/0.56          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.36/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0)
% 0.36/0.56          | (v2_struct_0 @ X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B)
% 0.36/0.56         | ~ (v2_pre_topc @ sk_B)
% 0.36/0.56         | ~ (l1_pre_topc @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_C_1)
% 0.36/0.56         | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.36/0.56         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.36/0.56         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.36/0.56         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.36/0.56         | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.36/0.56         | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.56         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['59', '68'])).
% 0.36/0.56  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('72', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('73', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.56  thf('74', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('75', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('76', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('77', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_C_1)
% 0.36/0.56         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.36/0.56         | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('demod', [status(thm)],
% 0.36/0.56                ['69', '70', '71', '72', '73', '74', '75', '76'])).
% 0.36/0.56  thf('78', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_C_1)
% 0.36/0.56         | (v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_A)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.36/0.56         | (v2_struct_0 @ sk_C_1)
% 0.36/0.56         | (v2_struct_0 @ sk_B)))
% 0.36/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['56', '77'])).
% 0.36/0.56  thf('79', plain,
% 0.36/0.56      ((((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.36/0.56         | (v2_struct_0 @ sk_A)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_C_1)))
% 0.36/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['78'])).
% 0.36/0.56  thf('80', plain,
% 0.36/0.56      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.36/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.36/0.56      inference('split', [status(esa)], ['11'])).
% 0.36/0.56  thf('81', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_C_1)
% 0.36/0.56         | (v2_struct_0 @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_D)
% 0.36/0.56         | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.36/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['79', '80'])).
% 0.36/0.56  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('83', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.36/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.36/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['81', '82'])).
% 0.36/0.56  thf('84', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('85', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.36/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.36/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('clc', [status(thm)], ['83', '84'])).
% 0.36/0.56  thf('86', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('87', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_B))
% 0.36/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.36/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('clc', [status(thm)], ['85', '86'])).
% 0.36/0.56  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('89', plain,
% 0.36/0.56      (~
% 0.36/0.56       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.36/0.56       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['87', '88'])).
% 0.36/0.56  thf('90', plain,
% 0.36/0.56      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.36/0.56       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))),
% 0.36/0.56      inference('split', [status(esa)], ['9'])).
% 0.36/0.56  thf('91', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['15', '19', '89', '90'])).
% 0.36/0.56  thf('92', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['6', '91'])).
% 0.36/0.56  thf('93', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_E @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t81_tmap_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.56             ( l1_pre_topc @ B ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.56               ( ![D:$i]:
% 0.36/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.56                   ( ![E:$i]:
% 0.36/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.56                         ( v1_funct_2 @
% 0.36/0.56                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.56                         ( m1_subset_1 @
% 0.36/0.56                           E @ 
% 0.36/0.56                           ( k1_zfmisc_1 @
% 0.36/0.56                             ( k2_zfmisc_1 @
% 0.36/0.56                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.56                       ( ![F:$i]:
% 0.36/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.56                           ( ![G:$i]:
% 0.36/0.56                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.56                               ( ( ( ( F ) = ( G ) ) & 
% 0.36/0.56                                   ( m1_pre_topc @ D @ C ) & 
% 0.36/0.56                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.36/0.56                                 ( r1_tmap_1 @
% 0.36/0.56                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.36/0.56                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('94', plain,
% 0.36/0.56      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X20)
% 0.36/0.56          | ~ (v2_pre_topc @ X20)
% 0.36/0.56          | ~ (l1_pre_topc @ X20)
% 0.36/0.56          | (v2_struct_0 @ X21)
% 0.36/0.56          | ~ (m1_pre_topc @ X21 @ X22)
% 0.36/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.36/0.56          | ~ (m1_pre_topc @ X21 @ X24)
% 0.36/0.56          | ~ (r1_tmap_1 @ X24 @ X20 @ X25 @ X23)
% 0.36/0.56          | ((X23) != (X26))
% 0.36/0.56          | (r1_tmap_1 @ X21 @ X20 @ 
% 0.36/0.56             (k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25) @ X26)
% 0.36/0.56          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X21))
% 0.36/0.56          | ~ (m1_subset_1 @ X25 @ 
% 0.36/0.56               (k1_zfmisc_1 @ 
% 0.36/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))))
% 0.36/0.56          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))
% 0.36/0.56          | ~ (v1_funct_1 @ X25)
% 0.36/0.56          | ~ (m1_pre_topc @ X24 @ X22)
% 0.36/0.56          | (v2_struct_0 @ X24)
% 0.36/0.56          | ~ (l1_pre_topc @ X22)
% 0.36/0.56          | ~ (v2_pre_topc @ X22)
% 0.36/0.56          | (v2_struct_0 @ X22))),
% 0.36/0.56      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.36/0.56  thf('95', plain,
% 0.36/0.56      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X22)
% 0.36/0.56          | ~ (v2_pre_topc @ X22)
% 0.36/0.56          | ~ (l1_pre_topc @ X22)
% 0.36/0.56          | (v2_struct_0 @ X24)
% 0.36/0.56          | ~ (m1_pre_topc @ X24 @ X22)
% 0.36/0.56          | ~ (v1_funct_1 @ X25)
% 0.36/0.56          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))
% 0.36/0.56          | ~ (m1_subset_1 @ X25 @ 
% 0.36/0.56               (k1_zfmisc_1 @ 
% 0.36/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))))
% 0.36/0.56          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X21))
% 0.36/0.56          | (r1_tmap_1 @ X21 @ X20 @ 
% 0.36/0.56             (k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25) @ X26)
% 0.36/0.56          | ~ (r1_tmap_1 @ X24 @ X20 @ X25 @ X26)
% 0.36/0.56          | ~ (m1_pre_topc @ X21 @ X24)
% 0.36/0.56          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.36/0.56          | ~ (m1_pre_topc @ X21 @ X22)
% 0.36/0.56          | (v2_struct_0 @ X21)
% 0.36/0.56          | ~ (l1_pre_topc @ X20)
% 0.36/0.56          | ~ (v2_pre_topc @ X20)
% 0.36/0.56          | (v2_struct_0 @ X20))),
% 0.36/0.56      inference('simplify', [status(thm)], ['94'])).
% 0.36/0.56  thf('96', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.36/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.56          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.36/0.56          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.36/0.56             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.36/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_D)
% 0.36/0.56          | ~ (l1_pre_topc @ X1)
% 0.36/0.56          | ~ (v2_pre_topc @ X1)
% 0.36/0.56          | (v2_struct_0 @ X1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['93', '95'])).
% 0.36/0.56  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('99', plain,
% 0.36/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('100', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('101', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.36/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.36/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.56          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.36/0.56          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.36/0.56             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.36/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_D)
% 0.36/0.56          | ~ (l1_pre_topc @ X1)
% 0.36/0.56          | ~ (v2_pre_topc @ X1)
% 0.36/0.56          | (v2_struct_0 @ X1))),
% 0.36/0.56      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.36/0.56  thf('102', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | (v2_struct_0 @ sk_D)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.36/0.56          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.36/0.56             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.36/0.56          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['92', '101'])).
% 0.36/0.56  thf('103', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('104', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | (v2_struct_0 @ sk_D)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.36/0.56          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.36/0.56             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.36/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.56          | (v2_struct_0 @ X1)
% 0.36/0.56          | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['102', '103'])).
% 0.36/0.56  thf('105', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ sk_C_1)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.36/0.56          | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.56          | (v2_struct_0 @ sk_D)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0)
% 0.36/0.56          | (v2_struct_0 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['4', '104'])).
% 0.36/0.56  thf('106', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('107', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (v2_struct_0 @ sk_C_1)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.36/0.56          | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.36/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.56          | (v2_struct_0 @ sk_D)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | ~ (v2_pre_topc @ X0)
% 0.36/0.56          | (v2_struct_0 @ X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.36/0.56  thf('108', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_B)
% 0.36/0.56        | ~ (v2_pre_topc @ sk_B)
% 0.36/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.36/0.56        | (v2_struct_0 @ sk_D)
% 0.36/0.56        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.36/0.56        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.36/0.56        | (v2_struct_0 @ sk_C_1)
% 0.36/0.56        | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['1', '107'])).
% 0.36/0.56  thf('109', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('110', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('111', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('112', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_B)
% 0.36/0.56        | (v2_struct_0 @ sk_D)
% 0.36/0.56        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.36/0.56        | (v2_struct_0 @ sk_C_1)
% 0.36/0.56        | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 0.36/0.56  thf('113', plain,
% 0.36/0.56      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('114', plain,
% 0.36/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.36/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.36/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('115', plain,
% 0.36/0.56      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)))),
% 0.36/0.56      inference('split', [status(esa)], ['18'])).
% 0.36/0.56  thf('116', plain,
% 0.36/0.56      (~
% 0.36/0.56       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.36/0.56       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['114', '115'])).
% 0.36/0.56  thf('117', plain,
% 0.36/0.56      (~
% 0.36/0.56       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['15', '19', '89', '116'])).
% 0.36/0.56  thf('118', plain,
% 0.36/0.56      (~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.36/0.56          (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['113', '117'])).
% 0.36/0.56  thf('119', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_A)
% 0.36/0.56        | (v2_struct_0 @ sk_C_1)
% 0.36/0.56        | (v2_struct_0 @ sk_D)
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['112', '118'])).
% 0.36/0.56  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('121', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['119', '120'])).
% 0.36/0.56  thf('122', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('123', plain, (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D))),
% 0.36/0.56      inference('clc', [status(thm)], ['121', '122'])).
% 0.36/0.56  thf('124', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('125', plain, ((v2_struct_0 @ sk_D)),
% 0.36/0.56      inference('clc', [status(thm)], ['123', '124'])).
% 0.36/0.56  thf('126', plain, ($false), inference('demod', [status(thm)], ['0', '125'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
