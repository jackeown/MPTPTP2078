%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AJVnz8QGD6

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  190 (2494 expanded)
%              Number of leaves         :   42 ( 746 expanded)
%              Depth                    :   30
%              Number of atoms          : 1768 (57943 expanded)
%              Number of equality atoms :   70 (1590 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t56_tmap_1,conjecture,(
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
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( ( ( u1_struct_0 @ B )
                    = ( u1_struct_0 @ C ) )
                  & ( r1_tarski @ ( u1_pre_topc @ C ) @ ( u1_pre_topc @ B ) ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                      & ( v5_pre_topc @ D @ A @ B )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                   => ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                      & ( v5_pre_topc @ D @ A @ C )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( ( ( u1_struct_0 @ B )
                      = ( u1_struct_0 @ C ) )
                    & ( r1_tarski @ ( u1_pre_topc @ C ) @ ( u1_pre_topc @ B ) ) )
                 => ! [D: $i] :
                      ( ( ( v1_funct_1 @ D )
                        & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( v5_pre_topc @ D @ A @ B )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( v1_funct_1 @ D )
                        & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                        & ( v5_pre_topc @ D @ A @ C )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_tmap_1])).

thf('0',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('9',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t55_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( v5_pre_topc @ C @ A @ B )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( v3_pre_topc @ D @ B )
                       => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( ( k2_struct_0 @ B )
          = k1_xboole_0 )
       => ( ( k2_struct_0 @ A )
          = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( ( k2_struct_0 @ X9 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('27',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('29',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v5_pre_topc @ C @ A @ B )
      <=> ! [D: $i] :
            ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
       => ( ( v3_pre_topc @ D @ B )
         => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( zip_tseitin_0 @ B @ A )
               => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_2 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ( zip_tseitin_2 @ X1 @ sk_C_1 @ X0 )
      | ~ ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ( zip_tseitin_2 @ X1 @ sk_C_1 @ X0 )
      | ~ ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('40',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','41','42'])).

thf('44',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','43'])).

thf('45',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('46',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('48',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X11 @ X14 @ X12 @ X15 )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X6 )
      | ( r2_hidden @ X5 @ ( u1_pre_topc @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1 )
      | ~ ( v3_pre_topc @ X0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X11 @ X14 @ X12 @ X15 )
      | ( v3_pre_topc @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C_1 ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('63',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X5 @ ( u1_pre_topc @ X6 ) )
      | ( v3_pre_topc @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_1 @ X0 @ X4 @ sk_C_1 @ X3 )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ sk_C_1 @ X0 )
      | ( v3_pre_topc @ X2 @ sk_B ) ) ),
    inference(condensation,[status(thm)],['69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X16 @ X17 @ X18 ) @ X18 @ X17 @ X16 )
      | ( v5_pre_topc @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_2 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ X1 ) @ sk_B )
      | ~ ( zip_tseitin_2 @ X1 @ sk_C_1 @ X0 )
      | ( v5_pre_topc @ X1 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','72'])).

thf('74',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('77',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('78',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('79',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('81',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['73','81'])).

thf('83',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('85',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X16 @ X17 @ X18 ) @ X18 @ X17 @ X16 )
      | ( v5_pre_topc @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_2 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( zip_tseitin_2 @ X1 @ sk_C_1 @ X0 )
      | ( v5_pre_topc @ X1 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('89',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('91',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) @ X14 @ X11 ) @ X13 )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ~ ( zip_tseitin_1 @ X11 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ sk_B ) @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ X0 )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ X0 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('99',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['73','81'])).

thf('100',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( ( k2_struct_0 @ X9 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('102',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_2 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('108',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('109',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('112',plain,
    ( ~ ( zip_tseitin_0 @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','107','108','109','110','111'])).

thf('113',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['100','112'])).

thf('114',plain,(
    v5_pre_topc @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v5_pre_topc @ X18 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X19 @ X18 @ X17 @ X16 )
      | ~ ( zip_tseitin_2 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X11 @ X14 @ X12 @ X15 )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('119',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) @ X14 @ X11 ) @ X13 )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ~ ( zip_tseitin_1 @ X11 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_1 @ X1 @ X5 @ X0 @ X4 )
      | ~ ( zip_tseitin_1 @ X1 @ X3 @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ X0 ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_D_1 @ X0 ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('127',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X11 @ X14 @ X12 @ X15 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) @ X14 @ X11 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X2 @ X1 ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ X2 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 )
      | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_D_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X16 @ X17 @ X18 ) @ X18 @ X17 @ X16 )
      | ( v5_pre_topc @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_2 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A )
      | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 )
      | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['97','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X2 @ X1 ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ X2 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X16 @ X17 @ X18 ) @ X18 @ X17 @ X16 )
      | ( v5_pre_topc @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_2 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('140',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('142',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('144',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['142','143'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('145',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['20','144','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AJVnz8QGD6
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:32:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.58  % Solved by: fo/fo7.sh
% 0.19/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.58  % done 248 iterations in 0.133s
% 0.19/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.58  % SZS output start Refutation
% 0.19/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.19/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.19/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.19/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.19/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.58  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.19/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.58  thf(t56_tmap_1, conjecture,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.58       ( ![B:$i]:
% 0.19/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.58             ( l1_pre_topc @ B ) ) =>
% 0.19/0.58           ( ![C:$i]:
% 0.19/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.19/0.58                 ( l1_pre_topc @ C ) ) =>
% 0.19/0.58               ( ( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ C ) ) & 
% 0.19/0.58                   ( r1_tarski @ ( u1_pre_topc @ C ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.19/0.58                 ( ![D:$i]:
% 0.19/0.58                   ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.58                       ( v1_funct_2 @
% 0.19/0.58                         D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.58                       ( v5_pre_topc @ D @ A @ B ) & 
% 0.19/0.58                       ( m1_subset_1 @
% 0.19/0.58                         D @ 
% 0.19/0.58                         ( k1_zfmisc_1 @
% 0.19/0.58                           ( k2_zfmisc_1 @
% 0.19/0.58                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.58                     ( ( v1_funct_1 @ D ) & 
% 0.19/0.58                       ( v1_funct_2 @
% 0.19/0.58                         D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.19/0.58                       ( v5_pre_topc @ D @ A @ C ) & 
% 0.19/0.58                       ( m1_subset_1 @
% 0.19/0.58                         D @ 
% 0.19/0.58                         ( k1_zfmisc_1 @
% 0.19/0.58                           ( k2_zfmisc_1 @
% 0.19/0.58                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.58    (~( ![A:$i]:
% 0.19/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.58            ( l1_pre_topc @ A ) ) =>
% 0.19/0.58          ( ![B:$i]:
% 0.19/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.58                ( l1_pre_topc @ B ) ) =>
% 0.19/0.58              ( ![C:$i]:
% 0.19/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.19/0.58                    ( l1_pre_topc @ C ) ) =>
% 0.19/0.58                  ( ( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ C ) ) & 
% 0.19/0.58                      ( r1_tarski @ ( u1_pre_topc @ C ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.19/0.58                    ( ![D:$i]:
% 0.19/0.58                      ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.58                          ( v1_funct_2 @
% 0.19/0.58                            D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.58                          ( v5_pre_topc @ D @ A @ B ) & 
% 0.19/0.58                          ( m1_subset_1 @
% 0.19/0.58                            D @ 
% 0.19/0.58                            ( k1_zfmisc_1 @
% 0.19/0.58                              ( k2_zfmisc_1 @
% 0.19/0.58                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.58                        ( ( v1_funct_1 @ D ) & 
% 0.19/0.58                          ( v1_funct_2 @
% 0.19/0.58                            D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.19/0.58                          ( v5_pre_topc @ D @ A @ C ) & 
% 0.19/0.58                          ( m1_subset_1 @
% 0.19/0.58                            D @ 
% 0.19/0.58                            ( k1_zfmisc_1 @
% 0.19/0.58                              ( k2_zfmisc_1 @
% 0.19/0.58                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.58    inference('cnf.neg', [status(esa)], [t56_tmap_1])).
% 0.19/0.58  thf('0', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(d3_struct_0, axiom,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.58  thf('1', plain,
% 0.19/0.58      (![X4 : $i]:
% 0.19/0.58         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.19/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.58  thf('2', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B))
% 0.19/0.58        | ~ (l1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.58  thf('3', plain, ((l1_pre_topc @ sk_C_1)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(dt_l1_pre_topc, axiom,
% 0.19/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.58  thf('4', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.19/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.58  thf('5', plain, ((l1_struct_0 @ sk_C_1)),
% 0.19/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.58  thf('6', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.58  thf('7', plain,
% 0.19/0.58      (![X4 : $i]:
% 0.19/0.58         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.19/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.58  thf('8', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.58  thf('9', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_B))
% 0.19/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.58  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('11', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.19/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.58  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.58  thf('13', plain, (((k2_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['9', '12'])).
% 0.19/0.58  thf('14', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['6', '13'])).
% 0.19/0.58  thf(fc2_struct_0, axiom,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.58  thf('15', plain,
% 0.19/0.58      (![X8 : $i]:
% 0.19/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.19/0.58          | ~ (l1_struct_0 @ X8)
% 0.19/0.58          | (v2_struct_0 @ X8))),
% 0.19/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.58  thf('16', plain,
% 0.19/0.58      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.19/0.58        | (v2_struct_0 @ sk_B)
% 0.19/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.58  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.58  thf('18', plain,
% 0.19/0.58      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.58  thf('19', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('20', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 0.19/0.58      inference('clc', [status(thm)], ['18', '19'])).
% 0.19/0.58  thf(t55_tops_2, axiom,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( l1_pre_topc @ A ) =>
% 0.19/0.58       ( ![B:$i]:
% 0.19/0.58         ( ( l1_pre_topc @ B ) =>
% 0.19/0.58           ( ![C:$i]:
% 0.19/0.58             ( ( ( m1_subset_1 @
% 0.19/0.58                   C @ 
% 0.19/0.58                   ( k1_zfmisc_1 @
% 0.19/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.19/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.58                 ( v1_funct_1 @ C ) ) =>
% 0.19/0.58               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.58                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.58                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.19/0.58                   ( ![D:$i]:
% 0.19/0.58                     ( ( m1_subset_1 @
% 0.19/0.58                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.58                       ( ( v3_pre_topc @ D @ B ) =>
% 0.19/0.58                         ( v3_pre_topc @
% 0.19/0.58                           ( k8_relset_1 @
% 0.19/0.58                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.19/0.58                           A ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.58  thf(zf_stmt_1, axiom,
% 0.19/0.58    (![B:$i,A:$i]:
% 0.19/0.58     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.58         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.19/0.58  thf('21', plain,
% 0.19/0.58      (![X9 : $i, X10 : $i]:
% 0.19/0.58         ((zip_tseitin_0 @ X9 @ X10) | ((k2_struct_0 @ X9) = (k1_xboole_0)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.58  thf('22', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.58        (k1_zfmisc_1 @ 
% 0.19/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('23', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['6', '13'])).
% 0.19/0.58  thf('24', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.58        (k1_zfmisc_1 @ 
% 0.19/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.19/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.58  thf('25', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('26', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.58  thf('27', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.58  thf('28', plain, (((k2_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['9', '12'])).
% 0.19/0.58  thf('29', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.58  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.19/0.58  thf(zf_stmt_3, axiom,
% 0.19/0.58    (![C:$i,B:$i,A:$i]:
% 0.19/0.58     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.19/0.58       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.19/0.58         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 0.19/0.58  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.19/0.58  thf(zf_stmt_5, axiom,
% 0.19/0.58    (![D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.58     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.19/0.58       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.58         ( ( v3_pre_topc @ D @ B ) =>
% 0.19/0.58           ( v3_pre_topc @
% 0.19/0.58             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.19/0.58             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 0.19/0.58  thf(zf_stmt_7, axiom,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( l1_pre_topc @ A ) =>
% 0.19/0.58       ( ![B:$i]:
% 0.19/0.58         ( ( l1_pre_topc @ B ) =>
% 0.19/0.58           ( ![C:$i]:
% 0.19/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.58                 ( m1_subset_1 @
% 0.19/0.58                   C @ 
% 0.19/0.58                   ( k1_zfmisc_1 @
% 0.19/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.58               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 0.19/0.58  thf('30', plain,
% 0.19/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.58         (~ (l1_pre_topc @ X20)
% 0.19/0.58          | ~ (zip_tseitin_0 @ X20 @ X21)
% 0.19/0.58          | (zip_tseitin_2 @ X22 @ X20 @ X21)
% 0.19/0.58          | ~ (m1_subset_1 @ X22 @ 
% 0.19/0.58               (k1_zfmisc_1 @ 
% 0.19/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))))
% 0.19/0.58          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.19/0.58          | ~ (v1_funct_1 @ X22)
% 0.19/0.58          | ~ (l1_pre_topc @ X21))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.19/0.58  thf('31', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X1 @ 
% 0.19/0.58             (k1_zfmisc_1 @ 
% 0.19/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))))
% 0.19/0.58          | ~ (l1_pre_topc @ X0)
% 0.19/0.58          | ~ (v1_funct_1 @ X1)
% 0.19/0.58          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C_1))
% 0.19/0.58          | (zip_tseitin_2 @ X1 @ sk_C_1 @ X0)
% 0.19/0.58          | ~ (zip_tseitin_0 @ sk_C_1 @ X0)
% 0.19/0.58          | ~ (l1_pre_topc @ sk_C_1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.58  thf('32', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.58  thf('33', plain, ((l1_pre_topc @ sk_C_1)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('34', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X1 @ 
% 0.19/0.58             (k1_zfmisc_1 @ 
% 0.19/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))))
% 0.19/0.58          | ~ (l1_pre_topc @ X0)
% 0.19/0.58          | ~ (v1_funct_1 @ X1)
% 0.19/0.58          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 0.19/0.58          | (zip_tseitin_2 @ X1 @ sk_C_1 @ X0)
% 0.19/0.58          | ~ (zip_tseitin_0 @ sk_C_1 @ X0))),
% 0.19/0.58      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.19/0.58  thf('35', plain,
% 0.19/0.58      ((~ (zip_tseitin_0 @ sk_C_1 @ sk_A)
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A)
% 0.19/0.58        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.19/0.58        | ~ (v1_funct_1 @ sk_D_1)
% 0.19/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.58      inference('sup-', [status(thm)], ['24', '34'])).
% 0.19/0.58  thf('36', plain,
% 0.19/0.58      (![X4 : $i]:
% 0.19/0.58         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.19/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.58  thf('37', plain,
% 0.19/0.58      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('38', plain,
% 0.19/0.58      (((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.19/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.58      inference('sup+', [status(thm)], ['36', '37'])).
% 0.19/0.58  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.58  thf('40', plain,
% 0.19/0.58      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.58  thf('41', plain, ((v1_funct_1 @ sk_D_1)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('43', plain,
% 0.19/0.58      ((~ (zip_tseitin_0 @ sk_C_1 @ sk_A)
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.19/0.58      inference('demod', [status(thm)], ['35', '40', '41', '42'])).
% 0.19/0.58  thf('44', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.19/0.58      inference('sup-', [status(thm)], ['21', '43'])).
% 0.19/0.58  thf('45', plain, (((k2_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['9', '12'])).
% 0.19/0.58  thf('46', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.19/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.58  thf('47', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.58  thf('48', plain,
% 0.19/0.58      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X11 @ X14 @ X12 @ X15)
% 0.19/0.58          | (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.58  thf('49', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | (zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1))),
% 0.19/0.58      inference('sup+', [status(thm)], ['47', '48'])).
% 0.19/0.58  thf('50', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.58  thf(d5_pre_topc, axiom,
% 0.19/0.58    (![A:$i]:
% 0.19/0.58     ( ( l1_pre_topc @ A ) =>
% 0.19/0.58       ( ![B:$i]:
% 0.19/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.58           ( ( v3_pre_topc @ B @ A ) <=>
% 0.19/0.58             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.19/0.58  thf('51', plain,
% 0.19/0.58      (![X5 : $i, X6 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.19/0.58          | ~ (v3_pre_topc @ X5 @ X6)
% 0.19/0.58          | (r2_hidden @ X5 @ (u1_pre_topc @ X6))
% 0.19/0.58          | ~ (l1_pre_topc @ X6))),
% 0.19/0.58      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.19/0.58  thf('52', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | ~ (l1_pre_topc @ sk_C_1)
% 0.19/0.58          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_C_1))
% 0.19/0.58          | ~ (v3_pre_topc @ X0 @ sk_C_1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.58  thf('53', plain, ((l1_pre_topc @ sk_C_1)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('54', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_C_1))
% 0.19/0.58          | ~ (v3_pre_topc @ X0 @ sk_C_1))),
% 0.19/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.19/0.58  thf('55', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1)
% 0.19/0.58          | ~ (v3_pre_topc @ X0 @ sk_C_1)
% 0.19/0.58          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_C_1)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['49', '54'])).
% 0.19/0.58  thf('56', plain,
% 0.19/0.58      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X11 @ X14 @ X12 @ X15) | (v3_pre_topc @ X11 @ X12))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.58  thf('57', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((r2_hidden @ X0 @ (u1_pre_topc @ sk_C_1))
% 0.19/0.58          | (zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1))),
% 0.19/0.58      inference('clc', [status(thm)], ['55', '56'])).
% 0.19/0.58  thf('58', plain,
% 0.19/0.58      ((r1_tarski @ (u1_pre_topc @ sk_C_1) @ (u1_pre_topc @ sk_B))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(d3_tarski, axiom,
% 0.19/0.58    (![A:$i,B:$i]:
% 0.19/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.58  thf('59', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.58          | (r2_hidden @ X0 @ X2)
% 0.19/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.58  thf('60', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((r2_hidden @ X0 @ (u1_pre_topc @ sk_B))
% 0.19/0.58          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_C_1)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.58  thf('61', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1)
% 0.19/0.58          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['57', '60'])).
% 0.19/0.58  thf('62', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | (zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1))),
% 0.19/0.58      inference('sup+', [status(thm)], ['47', '48'])).
% 0.19/0.58  thf('63', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['6', '13'])).
% 0.19/0.58  thf('64', plain,
% 0.19/0.58      (![X5 : $i, X6 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.19/0.58          | ~ (r2_hidden @ X5 @ (u1_pre_topc @ X6))
% 0.19/0.58          | (v3_pre_topc @ X5 @ X6)
% 0.19/0.58          | ~ (l1_pre_topc @ X6))),
% 0.19/0.58      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.19/0.58  thf('65', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.58          | (v3_pre_topc @ X0 @ sk_B)
% 0.19/0.58          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.19/0.58  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('67', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | (v3_pre_topc @ X0 @ sk_B)
% 0.19/0.58          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.19/0.58      inference('demod', [status(thm)], ['65', '66'])).
% 0.19/0.58  thf('68', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1)
% 0.19/0.58          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B))
% 0.19/0.58          | (v3_pre_topc @ X0 @ sk_B))),
% 0.19/0.58      inference('sup-', [status(thm)], ['62', '67'])).
% 0.19/0.58  thf('69', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X0 @ X4 @ sk_C_1 @ X3)
% 0.19/0.58          | (v3_pre_topc @ X0 @ sk_B)
% 0.19/0.58          | (zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['61', '68'])).
% 0.19/0.58  thf('70', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X2 @ X1 @ sk_C_1 @ X0) | (v3_pre_topc @ X2 @ sk_B))),
% 0.19/0.58      inference('condensation', [status(thm)], ['69'])).
% 0.19/0.58  thf('71', plain,
% 0.19/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.58         (~ (zip_tseitin_1 @ (sk_D @ X16 @ X17 @ X18) @ X18 @ X17 @ X16)
% 0.19/0.58          | (v5_pre_topc @ X18 @ X16 @ X17)
% 0.19/0.58          | ~ (zip_tseitin_2 @ X18 @ X17 @ X16))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.58  thf('72', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ X1) @ sk_B)
% 0.19/0.58          | ~ (zip_tseitin_2 @ X1 @ sk_C_1 @ X0)
% 0.19/0.58          | (v5_pre_topc @ X1 @ X0 @ sk_C_1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.19/0.58  thf('73', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.19/0.58        | (v3_pre_topc @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B))),
% 0.19/0.58      inference('sup-', [status(thm)], ['46', '72'])).
% 0.19/0.58  thf('74', plain,
% 0.19/0.58      ((~ (v1_funct_1 @ sk_D_1)
% 0.19/0.58        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.58             (u1_struct_0 @ sk_C_1))
% 0.19/0.58        | ~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.19/0.58        | ~ (m1_subset_1 @ sk_D_1 @ 
% 0.19/0.58             (k1_zfmisc_1 @ 
% 0.19/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1)))))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('75', plain, ((v1_funct_1 @ sk_D_1)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('76', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.58  thf('77', plain,
% 0.19/0.58      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.58  thf('78', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.58  thf('79', plain,
% 0.19/0.58      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.19/0.58        | ~ (m1_subset_1 @ sk_D_1 @ 
% 0.19/0.58             (k1_zfmisc_1 @ 
% 0.19/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 0.19/0.58      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 0.19/0.58  thf('80', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.58        (k1_zfmisc_1 @ 
% 0.19/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.19/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.58  thf('81', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)),
% 0.19/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.19/0.58  thf('82', plain,
% 0.19/0.58      (((v3_pre_topc @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.19/0.58        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.58      inference('clc', [status(thm)], ['73', '81'])).
% 0.19/0.58  thf('83', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.19/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.58  thf('84', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | (zip_tseitin_1 @ X0 @ X2 @ sk_C_1 @ X1))),
% 0.19/0.58      inference('sup+', [status(thm)], ['47', '48'])).
% 0.19/0.58  thf('85', plain,
% 0.19/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.58         (~ (zip_tseitin_1 @ (sk_D @ X16 @ X17 @ X18) @ X18 @ X17 @ X16)
% 0.19/0.58          | (v5_pre_topc @ X18 @ X16 @ X17)
% 0.19/0.58          | ~ (zip_tseitin_2 @ X18 @ X17 @ X16))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.58  thf('86', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ X1) @ 
% 0.19/0.58           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | ~ (zip_tseitin_2 @ X1 @ sk_C_1 @ X0)
% 0.19/0.58          | (v5_pre_topc @ X1 @ X0 @ sk_C_1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['84', '85'])).
% 0.19/0.58  thf('87', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.19/0.58        | (m1_subset_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ 
% 0.19/0.58           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B))))),
% 0.19/0.58      inference('sup-', [status(thm)], ['83', '86'])).
% 0.19/0.58  thf('88', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)),
% 0.19/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.19/0.58  thf('89', plain,
% 0.19/0.58      (((m1_subset_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ 
% 0.19/0.58         (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.58      inference('clc', [status(thm)], ['87', '88'])).
% 0.19/0.58  thf('90', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['6', '13'])).
% 0.19/0.58  thf('91', plain,
% 0.19/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12) @ X14 @ 
% 0.19/0.58              X11) @ 
% 0.19/0.58             X13)
% 0.19/0.58          | ~ (v3_pre_topc @ X11 @ X12)
% 0.19/0.58          | ~ (zip_tseitin_1 @ X11 @ X14 @ X12 @ X13))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.58  thf('92', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | ~ (zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1)
% 0.19/0.58          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ X2 @ X0) @ 
% 0.19/0.58             X1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['90', '91'])).
% 0.19/0.58  thf('93', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['6', '13'])).
% 0.19/0.58  thf('94', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.19/0.58          | ~ (zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1)
% 0.19/0.58          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ sk_B) @ X2 @ X0) @ 
% 0.19/0.58             X1))),
% 0.19/0.58      inference('demod', [status(thm)], ['92', '93'])).
% 0.19/0.58  thf('95', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X1 @ 
% 0.19/0.58              (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.19/0.58             X0)
% 0.19/0.58          | ~ (v3_pre_topc @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.19/0.58          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['89', '94'])).
% 0.19/0.58  thf('96', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0)
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X1 @ 
% 0.19/0.58              (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.19/0.58             X0)
% 0.19/0.58          | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['82', '95'])).
% 0.19/0.58  thf('97', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((v3_pre_topc @ 
% 0.19/0.58           (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X1 @ 
% 0.19/0.58            (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.19/0.58           X0)
% 0.19/0.58          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0)
% 0.19/0.58          | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.58      inference('simplify', [status(thm)], ['96'])).
% 0.19/0.58  thf('98', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.19/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.58  thf('99', plain,
% 0.19/0.58      (((v3_pre_topc @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.19/0.58        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.58      inference('clc', [status(thm)], ['73', '81'])).
% 0.19/0.58  thf('100', plain,
% 0.19/0.58      (![X9 : $i, X10 : $i]:
% 0.19/0.58         ((zip_tseitin_0 @ X9 @ X10) | ((k2_struct_0 @ X9) = (k1_xboole_0)))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.58  thf('101', plain,
% 0.19/0.58      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.58        (k1_zfmisc_1 @ 
% 0.19/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.19/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.58  thf('102', plain,
% 0.19/0.58      (![X4 : $i]:
% 0.19/0.58         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.19/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.58  thf('103', plain,
% 0.19/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.58         (~ (l1_pre_topc @ X20)
% 0.19/0.58          | ~ (zip_tseitin_0 @ X20 @ X21)
% 0.19/0.58          | (zip_tseitin_2 @ X22 @ X20 @ X21)
% 0.19/0.58          | ~ (m1_subset_1 @ X22 @ 
% 0.19/0.58               (k1_zfmisc_1 @ 
% 0.19/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))))
% 0.19/0.58          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.19/0.58          | ~ (v1_funct_1 @ X22)
% 0.19/0.58          | ~ (l1_pre_topc @ X21))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.19/0.58  thf('104', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X2 @ 
% 0.19/0.58             (k1_zfmisc_1 @ 
% 0.19/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.19/0.58          | ~ (l1_struct_0 @ X0)
% 0.19/0.58          | ~ (l1_pre_topc @ X1)
% 0.19/0.58          | ~ (v1_funct_1 @ X2)
% 0.19/0.58          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.19/0.58          | (zip_tseitin_2 @ X2 @ X0 @ X1)
% 0.19/0.58          | ~ (zip_tseitin_0 @ X0 @ X1)
% 0.19/0.58          | ~ (l1_pre_topc @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['102', '103'])).
% 0.19/0.58  thf('105', plain,
% 0.19/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.19/0.58        | ~ (zip_tseitin_0 @ sk_B @ sk_A)
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.19/0.58        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.58        | ~ (v1_funct_1 @ sk_D_1)
% 0.19/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.58      inference('sup-', [status(thm)], ['101', '104'])).
% 0.19/0.58  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('107', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['6', '13'])).
% 0.19/0.58  thf('108', plain,
% 0.19/0.58      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.58  thf('109', plain, ((v1_funct_1 @ sk_D_1)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('111', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.58  thf('112', plain,
% 0.19/0.58      ((~ (zip_tseitin_0 @ sk_B @ sk_A)
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.19/0.58      inference('demod', [status(thm)],
% 0.19/0.58                ['105', '106', '107', '108', '109', '110', '111'])).
% 0.19/0.58  thf('113', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.19/0.58      inference('sup-', [status(thm)], ['100', '112'])).
% 0.19/0.58  thf('114', plain, ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_B)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('115', plain,
% 0.19/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.58         (~ (v5_pre_topc @ X18 @ X16 @ X17)
% 0.19/0.58          | (zip_tseitin_1 @ X19 @ X18 @ X17 @ X16)
% 0.19/0.58          | ~ (zip_tseitin_2 @ X18 @ X17 @ X16))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.58  thf('116', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         (~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.19/0.58          | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ sk_A))),
% 0.19/0.58      inference('sup-', [status(thm)], ['114', '115'])).
% 0.19/0.58  thf('117', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ sk_A))),
% 0.19/0.58      inference('sup-', [status(thm)], ['113', '116'])).
% 0.19/0.58  thf('118', plain,
% 0.19/0.58      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X11 @ X14 @ X12 @ X15)
% 0.19/0.58          | (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.58  thf('119', plain,
% 0.19/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12) @ X14 @ 
% 0.19/0.58              X11) @ 
% 0.19/0.58             X13)
% 0.19/0.58          | ~ (v3_pre_topc @ X11 @ X12)
% 0.19/0.58          | ~ (zip_tseitin_1 @ X11 @ X14 @ X12 @ X13))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.58  thf('120', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X1 @ X5 @ X0 @ X4)
% 0.19/0.58          | ~ (zip_tseitin_1 @ X1 @ X3 @ X0 @ X2)
% 0.19/0.58          | ~ (v3_pre_topc @ X1 @ X0)
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ X1) @ 
% 0.19/0.58             X2))),
% 0.19/0.58      inference('sup-', [status(thm)], ['118', '119'])).
% 0.19/0.58  thf('121', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.58              sk_D_1 @ X0) @ 
% 0.19/0.58             sk_A)
% 0.19/0.58          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.19/0.58          | (zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['117', '120'])).
% 0.19/0.58  thf('122', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.19/0.58      inference('demod', [status(thm)], ['6', '13'])).
% 0.19/0.58  thf('123', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.19/0.58              sk_D_1 @ X0) @ 
% 0.19/0.58             sk_A)
% 0.19/0.58          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.19/0.58          | (zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1))),
% 0.19/0.58      inference('demod', [status(thm)], ['121', '122'])).
% 0.19/0.58  thf('124', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0)
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.19/0.58              sk_D_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.19/0.58             sk_A)
% 0.19/0.58          | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['99', '123'])).
% 0.19/0.58  thf('125', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((v3_pre_topc @ 
% 0.19/0.58           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.19/0.58            sk_D_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.19/0.58           sk_A)
% 0.19/0.58          | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0)
% 0.19/0.58          | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.58      inference('simplify', [status(thm)], ['124'])).
% 0.19/0.58  thf('126', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.19/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.58  thf('127', plain,
% 0.19/0.58      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ X11 @ X14 @ X12 @ X15)
% 0.19/0.58          | ~ (v3_pre_topc @ 
% 0.19/0.58               (k8_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 0.19/0.58                X14 @ X11) @ 
% 0.19/0.58               X15))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.58  thf('128', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (~ (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X2 @ X1) @ 
% 0.19/0.58             X0)
% 0.19/0.58          | (zip_tseitin_1 @ X1 @ X2 @ sk_C_1 @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['126', '127'])).
% 0.19/0.58  thf('129', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0)
% 0.19/0.58          | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ sk_D_1 @ 
% 0.19/0.58             sk_C_1 @ sk_A))),
% 0.19/0.58      inference('sup-', [status(thm)], ['125', '128'])).
% 0.19/0.58  thf('130', plain,
% 0.19/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.58         (~ (zip_tseitin_1 @ (sk_D @ X16 @ X17 @ X18) @ X18 @ X17 @ X16)
% 0.19/0.58          | (v5_pre_topc @ X18 @ X16 @ X17)
% 0.19/0.58          | ~ (zip_tseitin_2 @ X18 @ X17 @ X16))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.58  thf('131', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0)
% 0.19/0.58          | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | ~ (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A)
% 0.19/0.58          | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['129', '130'])).
% 0.19/0.58  thf('132', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.19/0.58          | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['98', '131'])).
% 0.19/0.58  thf('133', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0)
% 0.19/0.58          | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.19/0.58          | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.58      inference('simplify', [status(thm)], ['132'])).
% 0.19/0.58  thf('134', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)),
% 0.19/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.19/0.58  thf('135', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_B @ X0))),
% 0.19/0.58      inference('clc', [status(thm)], ['133', '134'])).
% 0.19/0.58  thf('136', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X1 @ 
% 0.19/0.58              (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.19/0.58             X0))),
% 0.19/0.58      inference('clc', [status(thm)], ['97', '135'])).
% 0.19/0.58  thf('137', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (~ (v3_pre_topc @ 
% 0.19/0.58             (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X2 @ X1) @ 
% 0.19/0.58             X0)
% 0.19/0.58          | (zip_tseitin_1 @ X1 @ X2 @ sk_C_1 @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['126', '127'])).
% 0.19/0.58  thf('138', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58          | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_C_1 @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['136', '137'])).
% 0.19/0.58  thf('139', plain,
% 0.19/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.58         (~ (zip_tseitin_1 @ (sk_D @ X16 @ X17 @ X18) @ X18 @ X17 @ X16)
% 0.19/0.58          | (v5_pre_topc @ X18 @ X16 @ X17)
% 0.19/0.58          | ~ (zip_tseitin_2 @ X18 @ X17 @ X16))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.58  thf('140', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58        | ~ (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A)
% 0.19/0.58        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['138', '139'])).
% 0.19/0.58  thf('141', plain,
% 0.19/0.58      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.19/0.58        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.19/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.58  thf('142', plain,
% 0.19/0.58      (((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.19/0.58        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.19/0.58      inference('clc', [status(thm)], ['140', '141'])).
% 0.19/0.58  thf('143', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)),
% 0.19/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.19/0.58  thf('144', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.19/0.58      inference('clc', [status(thm)], ['142', '143'])).
% 0.19/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.58  thf('145', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.58  thf('146', plain, ($false),
% 0.19/0.58      inference('demod', [status(thm)], ['20', '144', '145'])).
% 0.19/0.58  
% 0.19/0.58  % SZS output end Refutation
% 0.19/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
