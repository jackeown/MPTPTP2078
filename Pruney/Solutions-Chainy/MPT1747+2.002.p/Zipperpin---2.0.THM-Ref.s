%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nDmaNA4Xx4

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:37 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  195 (1401 expanded)
%              Number of leaves         :   43 ( 423 expanded)
%              Depth                    :   26
%              Number of atoms          : 1689 (33251 expanded)
%              Number of equality atoms :   61 ( 852 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

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
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('9',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_struct_0 @ sk_C )
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
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( ( k2_struct_0 @ X11 )
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

thf('25',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('31',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('35',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,
    ( ~ ( zip_tseitin_0 @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','35','36','37','38'])).

thf('40',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','39'])).

thf('41',plain,(
    v5_pre_topc @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( v5_pre_topc @ X20 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X21 @ X20 @ X19 @ X18 )
      | ~ ( zip_tseitin_2 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( ( k2_struct_0 @ X11 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('47',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('49',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('51',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ( zip_tseitin_2 @ X1 @ sk_C @ X0 )
      | ~ ( zip_tseitin_0 @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('55',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ( zip_tseitin_2 @ X1 @ sk_C @ X0 )
      | ~ ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( zip_tseitin_0 @ sk_C @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('59',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( zip_tseitin_0 @ sk_C @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['45','61'])).

thf('63',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('64',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X13 @ X16 @ X14 @ X17 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ( v3_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('75',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('76',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1 )
      | ~ ( v3_pre_topc @ X0 @ sk_C )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X13 @ X16 @ X14 @ X17 )
      | ( v3_pre_topc @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1 ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_C ) @ ( u1_pre_topc @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('84',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v3_pre_topc @ X0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1 ) ) ),
    inference(clc,[status(thm)],['73','88'])).

thf('90',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X18 @ X19 @ X20 ) @ X20 @ X19 @ X18 )
      | ( v5_pre_topc @ X20 @ X18 @ X19 )
      | ~ ( zip_tseitin_2 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X0 @ sk_C @ X1 ) @ sk_B )
      | ~ ( zip_tseitin_2 @ X1 @ sk_C @ X0 )
      | ( v5_pre_topc @ X1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['64','91'])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(split,[status(esa)],['93'])).

thf('98',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
   <= ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('102',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('104',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(split,[status(esa)],['93'])).

thf('106',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('110',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(split,[status(esa)],['93'])).

thf('113',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['99','102','111','112'])).

thf('114',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['94','113'])).

thf('115',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['92','114'])).

thf('116',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('117',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('118',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X13 @ X16 @ X14 @ X17 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('119',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X0 @ X2 )
      | ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_B ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1 ) ) ),
    inference('sup+',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X18 @ X19 @ X20 ) @ X20 @ X19 @ X18 )
      | ( v5_pre_topc @ X20 @ X18 @ X19 )
      | ~ ( zip_tseitin_2 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_D @ X0 @ sk_C @ X1 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( zip_tseitin_2 @ X1 @ sk_C @ X0 )
      | ( v5_pre_topc @ X1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ( r1_tarski @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','123'])).

thf('125',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['94','113'])).

thf('126',plain,
    ( ( r1_tarski @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('130',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) @ X16 @ X13 ) @ X15 )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X13 @ X16 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ sk_B ) @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ X1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ X1 @ sk_B @ X0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ X0 )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ X0 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ X1 @ sk_B @ X0 )
      | ( ( k2_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','136'])).

thf('138',plain,
    ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ sk_A )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('140',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X13 @ X16 @ X14 @ X17 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X14 ) @ X16 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) @ X2 @ X1 ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ X2 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ sk_D_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X18 @ X19 @ X20 ) @ X20 @ X19 @ X18 )
      | ( v5_pre_topc @ X20 @ X18 @ X19 )
      | ~ ( zip_tseitin_2 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('144',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('146',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['94','113'])).

thf('148',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['146','147'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('149',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['20','148','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nDmaNA4Xx4
% 0.16/0.38  % Computer   : n012.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 18:58:52 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 346 iterations in 0.208s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.52/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.52/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.52/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.52/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.52/0.70  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.52/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.70  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.52/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.52/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.52/0.70  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.52/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.70  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.52/0.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.52/0.70  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.52/0.70  thf(t56_tmap_1, conjecture,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.52/0.70             ( l1_pre_topc @ B ) ) =>
% 0.52/0.70           ( ![C:$i]:
% 0.52/0.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.52/0.70                 ( l1_pre_topc @ C ) ) =>
% 0.52/0.70               ( ( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ C ) ) & 
% 0.52/0.70                   ( r1_tarski @ ( u1_pre_topc @ C ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.52/0.70                 ( ![D:$i]:
% 0.52/0.70                   ( ( ( v1_funct_1 @ D ) & 
% 0.52/0.70                       ( v1_funct_2 @
% 0.52/0.70                         D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.70                       ( v5_pre_topc @ D @ A @ B ) & 
% 0.52/0.70                       ( m1_subset_1 @
% 0.52/0.70                         D @ 
% 0.52/0.70                         ( k1_zfmisc_1 @
% 0.52/0.70                           ( k2_zfmisc_1 @
% 0.52/0.70                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.70                     ( ( v1_funct_1 @ D ) & 
% 0.52/0.70                       ( v1_funct_2 @
% 0.52/0.70                         D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.52/0.70                       ( v5_pre_topc @ D @ A @ C ) & 
% 0.52/0.70                       ( m1_subset_1 @
% 0.52/0.70                         D @ 
% 0.52/0.70                         ( k1_zfmisc_1 @
% 0.52/0.70                           ( k2_zfmisc_1 @
% 0.52/0.70                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i]:
% 0.52/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.52/0.70            ( l1_pre_topc @ A ) ) =>
% 0.52/0.70          ( ![B:$i]:
% 0.52/0.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.52/0.70                ( l1_pre_topc @ B ) ) =>
% 0.52/0.70              ( ![C:$i]:
% 0.52/0.70                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.52/0.70                    ( l1_pre_topc @ C ) ) =>
% 0.52/0.70                  ( ( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ C ) ) & 
% 0.52/0.70                      ( r1_tarski @ ( u1_pre_topc @ C ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.52/0.70                    ( ![D:$i]:
% 0.52/0.70                      ( ( ( v1_funct_1 @ D ) & 
% 0.52/0.70                          ( v1_funct_2 @
% 0.52/0.70                            D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.70                          ( v5_pre_topc @ D @ A @ B ) & 
% 0.52/0.70                          ( m1_subset_1 @
% 0.52/0.70                            D @ 
% 0.52/0.70                            ( k1_zfmisc_1 @
% 0.52/0.70                              ( k2_zfmisc_1 @
% 0.52/0.70                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.70                        ( ( v1_funct_1 @ D ) & 
% 0.52/0.70                          ( v1_funct_2 @
% 0.52/0.70                            D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.52/0.70                          ( v5_pre_topc @ D @ A @ C ) & 
% 0.52/0.70                          ( m1_subset_1 @
% 0.52/0.70                            D @ 
% 0.52/0.70                            ( k1_zfmisc_1 @
% 0.52/0.70                              ( k2_zfmisc_1 @
% 0.52/0.70                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t56_tmap_1])).
% 0.52/0.70  thf('0', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(d3_struct_0, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.52/0.70  thf('1', plain,
% 0.52/0.70      (![X6 : $i]:
% 0.52/0.70         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.52/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.70  thf('2', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_C))),
% 0.52/0.70      inference('sup+', [status(thm)], ['0', '1'])).
% 0.52/0.70  thf('3', plain, ((l1_pre_topc @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(dt_l1_pre_topc, axiom,
% 0.52/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.52/0.70  thf('4', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.70  thf('5', plain, ((l1_struct_0 @ sk_C)),
% 0.52/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.70  thf('6', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['2', '5'])).
% 0.52/0.70  thf('7', plain,
% 0.52/0.70      (![X6 : $i]:
% 0.52/0.70         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.52/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.70  thf('8', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['2', '5'])).
% 0.52/0.70  thf('9', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.70      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.70  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('11', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.70  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('13', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['9', '12'])).
% 0.52/0.70  thf('14', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['6', '13'])).
% 0.52/0.70  thf(fc2_struct_0, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.52/0.70       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.52/0.70  thf('15', plain,
% 0.52/0.70      (![X10 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.52/0.70          | ~ (l1_struct_0 @ X10)
% 0.52/0.70          | (v2_struct_0 @ X10))),
% 0.52/0.70      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.52/0.70  thf('16', plain,
% 0.52/0.70      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.52/0.70        | (v2_struct_0 @ sk_B)
% 0.52/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.70  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('18', plain,
% 0.52/0.70      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.52/0.70  thf('19', plain, (~ (v2_struct_0 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('20', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 0.52/0.70      inference('clc', [status(thm)], ['18', '19'])).
% 0.52/0.70  thf(t55_tops_2, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( l1_pre_topc @ A ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( l1_pre_topc @ B ) =>
% 0.52/0.70           ( ![C:$i]:
% 0.52/0.70             ( ( ( m1_subset_1 @
% 0.52/0.70                   C @ 
% 0.52/0.70                   ( k1_zfmisc_1 @
% 0.52/0.70                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.52/0.70                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.70                 ( v1_funct_1 @ C ) ) =>
% 0.52/0.70               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.70                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.70                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.52/0.70                   ( ![D:$i]:
% 0.52/0.70                     ( ( m1_subset_1 @
% 0.52/0.70                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.52/0.70                       ( ( v3_pre_topc @ D @ B ) =>
% 0.52/0.70                         ( v3_pre_topc @
% 0.52/0.70                           ( k8_relset_1 @
% 0.52/0.70                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.52/0.70                           A ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_1, axiom,
% 0.52/0.70    (![B:$i,A:$i]:
% 0.52/0.70     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.70         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.52/0.70  thf('21', plain,
% 0.52/0.70      (![X11 : $i, X12 : $i]:
% 0.52/0.70         ((zip_tseitin_0 @ X11 @ X12) | ((k2_struct_0 @ X11) = (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.70  thf('22', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70        (k1_zfmisc_1 @ 
% 0.52/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('23', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['6', '13'])).
% 0.52/0.70  thf('24', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70        (k1_zfmisc_1 @ 
% 0.52/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.52/0.70      inference('demod', [status(thm)], ['22', '23'])).
% 0.52/0.70  thf('25', plain,
% 0.52/0.70      (![X6 : $i]:
% 0.52/0.70         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.52/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.70  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.52/0.70  thf(zf_stmt_3, axiom,
% 0.52/0.70    (![C:$i,B:$i,A:$i]:
% 0.52/0.70     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.52/0.70       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.52/0.70         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.52/0.70  thf(zf_stmt_5, axiom,
% 0.52/0.70    (![D:$i,C:$i,B:$i,A:$i]:
% 0.52/0.70     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.52/0.70       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.52/0.70         ( ( v3_pre_topc @ D @ B ) =>
% 0.52/0.70           ( v3_pre_topc @
% 0.52/0.70             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.52/0.70             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 0.52/0.70  thf(zf_stmt_7, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( l1_pre_topc @ A ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( l1_pre_topc @ B ) =>
% 0.52/0.70           ( ![C:$i]:
% 0.52/0.70             ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.70                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.70                 ( m1_subset_1 @
% 0.52/0.70                   C @ 
% 0.52/0.70                   ( k1_zfmisc_1 @
% 0.52/0.70                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.70               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 0.52/0.70  thf('26', plain,
% 0.52/0.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.70         (~ (l1_pre_topc @ X22)
% 0.52/0.70          | ~ (zip_tseitin_0 @ X22 @ X23)
% 0.52/0.70          | (zip_tseitin_2 @ X24 @ X22 @ X23)
% 0.52/0.70          | ~ (m1_subset_1 @ X24 @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))))
% 0.52/0.70          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.52/0.70          | ~ (v1_funct_1 @ X24)
% 0.52/0.70          | ~ (l1_pre_topc @ X23))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.52/0.70  thf('27', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X2 @ 
% 0.52/0.70             (k1_zfmisc_1 @ 
% 0.52/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.52/0.70          | ~ (l1_struct_0 @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X1)
% 0.52/0.70          | ~ (v1_funct_1 @ X2)
% 0.52/0.70          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.52/0.70          | (zip_tseitin_2 @ X2 @ X0 @ X1)
% 0.52/0.70          | ~ (zip_tseitin_0 @ X0 @ X1)
% 0.52/0.70          | ~ (l1_pre_topc @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.52/0.70  thf('28', plain,
% 0.52/0.70      ((~ (l1_pre_topc @ sk_B)
% 0.52/0.70        | ~ (zip_tseitin_0 @ sk_B @ sk_A)
% 0.52/0.70        | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.52/0.70        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.52/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['24', '27'])).
% 0.52/0.70  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('30', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['6', '13'])).
% 0.52/0.70  thf('31', plain,
% 0.52/0.70      (![X6 : $i]:
% 0.52/0.70         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.52/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.70  thf('32', plain,
% 0.52/0.70      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('33', plain,
% 0.52/0.70      (((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.52/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.70      inference('sup+', [status(thm)], ['31', '32'])).
% 0.52/0.70  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('35', plain,
% 0.52/0.70      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.70  thf('36', plain, ((v1_funct_1 @ sk_D_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('39', plain,
% 0.52/0.70      ((~ (zip_tseitin_0 @ sk_B @ sk_A)
% 0.52/0.70        | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)],
% 0.52/0.70                ['28', '29', '30', '35', '36', '37', '38'])).
% 0.52/0.70  thf('40', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['21', '39'])).
% 0.52/0.70  thf('41', plain, ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('42', plain,
% 0.52/0.70      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.70         (~ (v5_pre_topc @ X20 @ X18 @ X19)
% 0.52/0.70          | (zip_tseitin_1 @ X21 @ X20 @ X19 @ X18)
% 0.52/0.70          | ~ (zip_tseitin_2 @ X20 @ X19 @ X18))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.70  thf('43', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.52/0.70          | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.52/0.70  thf('44', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70          | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['40', '43'])).
% 0.52/0.70  thf('45', plain,
% 0.52/0.70      (![X11 : $i, X12 : $i]:
% 0.52/0.70         ((zip_tseitin_0 @ X11 @ X12) | ((k2_struct_0 @ X11) = (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.70  thf('46', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70        (k1_zfmisc_1 @ 
% 0.52/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.52/0.70      inference('demod', [status(thm)], ['22', '23'])).
% 0.52/0.70  thf('47', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('48', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['2', '5'])).
% 0.52/0.70  thf('49', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['47', '48'])).
% 0.52/0.70  thf('50', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['9', '12'])).
% 0.52/0.70  thf('51', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.52/0.70  thf('52', plain,
% 0.52/0.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.70         (~ (l1_pre_topc @ X22)
% 0.52/0.70          | ~ (zip_tseitin_0 @ X22 @ X23)
% 0.52/0.70          | (zip_tseitin_2 @ X24 @ X22 @ X23)
% 0.52/0.70          | ~ (m1_subset_1 @ X24 @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))))
% 0.52/0.70          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.52/0.70          | ~ (v1_funct_1 @ X24)
% 0.52/0.70          | ~ (l1_pre_topc @ X23))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.52/0.70  thf('53', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X1 @ 
% 0.52/0.70             (k1_zfmisc_1 @ 
% 0.52/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ X1)
% 0.52/0.70          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C))
% 0.52/0.70          | (zip_tseitin_2 @ X1 @ sk_C @ X0)
% 0.52/0.70          | ~ (zip_tseitin_0 @ sk_C @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.52/0.70  thf('54', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.52/0.70  thf('55', plain, ((l1_pre_topc @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('56', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X1 @ 
% 0.52/0.70             (k1_zfmisc_1 @ 
% 0.52/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ X1)
% 0.52/0.70          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 0.52/0.70          | (zip_tseitin_2 @ X1 @ sk_C @ X0)
% 0.52/0.70          | ~ (zip_tseitin_0 @ sk_C @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.52/0.70  thf('57', plain,
% 0.52/0.70      ((~ (zip_tseitin_0 @ sk_C @ sk_A)
% 0.52/0.70        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A)
% 0.52/0.70        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.52/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.52/0.70        | ~ (l1_pre_topc @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['46', '56'])).
% 0.52/0.70  thf('58', plain,
% 0.52/0.70      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.70  thf('59', plain, ((v1_funct_1 @ sk_D_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('61', plain,
% 0.52/0.70      ((~ (zip_tseitin_0 @ sk_C @ sk_A)
% 0.52/0.70        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.52/0.70  thf('62', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.52/0.70        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['45', '61'])).
% 0.52/0.70  thf('63', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['9', '12'])).
% 0.52/0.70  thf('64', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.52/0.70  thf('65', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.52/0.70  thf('66', plain,
% 0.52/0.70      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.52/0.70         ((zip_tseitin_1 @ X13 @ X16 @ X14 @ X17)
% 0.52/0.70          | (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.70  thf('67', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.52/0.70          | (zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1))),
% 0.52/0.70      inference('sup+', [status(thm)], ['65', '66'])).
% 0.52/0.70  thf('68', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['6', '13'])).
% 0.52/0.70  thf(d5_pre_topc, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( l1_pre_topc @ A ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.70           ( ( v3_pre_topc @ B @ A ) <=>
% 0.52/0.70             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.52/0.70  thf('69', plain,
% 0.52/0.70      (![X7 : $i, X8 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.52/0.70          | ~ (r2_hidden @ X7 @ (u1_pre_topc @ X8))
% 0.52/0.70          | (v3_pre_topc @ X7 @ X8)
% 0.52/0.70          | ~ (l1_pre_topc @ X8))),
% 0.52/0.70      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.52/0.70  thf('70', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.52/0.70          | ~ (l1_pre_topc @ sk_B)
% 0.52/0.70          | (v3_pre_topc @ X0 @ sk_B)
% 0.52/0.70          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['68', '69'])).
% 0.52/0.70  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('72', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.52/0.70          | (v3_pre_topc @ X0 @ sk_B)
% 0.52/0.70          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.52/0.70      inference('demod', [status(thm)], ['70', '71'])).
% 0.52/0.70  thf('73', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1)
% 0.52/0.70          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B))
% 0.52/0.70          | (v3_pre_topc @ X0 @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['67', '72'])).
% 0.52/0.70  thf('74', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.52/0.70          | (zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1))),
% 0.52/0.70      inference('sup+', [status(thm)], ['65', '66'])).
% 0.52/0.70  thf('75', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.52/0.70  thf('76', plain,
% 0.52/0.70      (![X7 : $i, X8 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.52/0.70          | ~ (v3_pre_topc @ X7 @ X8)
% 0.52/0.70          | (r2_hidden @ X7 @ (u1_pre_topc @ X8))
% 0.52/0.70          | ~ (l1_pre_topc @ X8))),
% 0.52/0.70      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.52/0.70  thf('77', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.52/0.70          | ~ (l1_pre_topc @ sk_C)
% 0.52/0.70          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_C))
% 0.52/0.70          | ~ (v3_pre_topc @ X0 @ sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['75', '76'])).
% 0.52/0.70  thf('78', plain, ((l1_pre_topc @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('79', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.52/0.70          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_C))
% 0.52/0.70          | ~ (v3_pre_topc @ X0 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['77', '78'])).
% 0.52/0.70  thf('80', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1)
% 0.52/0.70          | ~ (v3_pre_topc @ X0 @ sk_C)
% 0.52/0.70          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_C)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['74', '79'])).
% 0.52/0.70  thf('81', plain,
% 0.52/0.70      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.52/0.70         ((zip_tseitin_1 @ X13 @ X16 @ X14 @ X17) | (v3_pre_topc @ X13 @ X14))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.70  thf('82', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((r2_hidden @ X0 @ (u1_pre_topc @ sk_C))
% 0.52/0.70          | (zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1))),
% 0.52/0.70      inference('clc', [status(thm)], ['80', '81'])).
% 0.52/0.70  thf('83', plain, ((r1_tarski @ (u1_pre_topc @ sk_C) @ (u1_pre_topc @ sk_B))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(t3_subset, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.70  thf('84', plain,
% 0.52/0.70      (![X3 : $i, X5 : $i]:
% 0.52/0.70         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.52/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.70  thf('85', plain,
% 0.52/0.70      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.52/0.70        (k1_zfmisc_1 @ (u1_pre_topc @ sk_B)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['83', '84'])).
% 0.52/0.70  thf(l3_subset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.52/0.70  thf('86', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.52/0.70          | (r2_hidden @ X0 @ X2)
% 0.52/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.52/0.70      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.52/0.70  thf('87', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ X0 @ (u1_pre_topc @ sk_B))
% 0.52/0.70          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_C)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['85', '86'])).
% 0.52/0.70  thf('88', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1)
% 0.52/0.70          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['82', '87'])).
% 0.52/0.70  thf('89', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((v3_pre_topc @ X0 @ sk_B) | (zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1))),
% 0.52/0.70      inference('clc', [status(thm)], ['73', '88'])).
% 0.52/0.70  thf('90', plain,
% 0.52/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.70         (~ (zip_tseitin_1 @ (sk_D @ X18 @ X19 @ X20) @ X20 @ X19 @ X18)
% 0.52/0.70          | (v5_pre_topc @ X20 @ X18 @ X19)
% 0.52/0.70          | ~ (zip_tseitin_2 @ X20 @ X19 @ X18))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.70  thf('91', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((v3_pre_topc @ (sk_D @ X0 @ sk_C @ X1) @ sk_B)
% 0.52/0.70          | ~ (zip_tseitin_2 @ X1 @ sk_C @ X0)
% 0.52/0.70          | (v5_pre_topc @ X1 @ X0 @ sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['89', '90'])).
% 0.52/0.70  thf('92', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)
% 0.52/0.70        | (v3_pre_topc @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['64', '91'])).
% 0.52/0.70  thf('93', plain,
% 0.52/0.70      ((~ (v1_funct_1 @ sk_D_1)
% 0.52/0.70        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))
% 0.52/0.70        | ~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70             (k1_zfmisc_1 @ 
% 0.52/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('94', plain,
% 0.52/0.70      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C))
% 0.52/0.70         <= (~ ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)))),
% 0.52/0.70      inference('split', [status(esa)], ['93'])).
% 0.52/0.70  thf('95', plain,
% 0.52/0.70      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('96', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('97', plain,
% 0.52/0.70      ((~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))
% 0.52/0.70         <= (~
% 0.52/0.70             ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.70               (u1_struct_0 @ sk_C))))),
% 0.52/0.70      inference('split', [status(esa)], ['93'])).
% 0.52/0.70  thf('98', plain,
% 0.52/0.70      ((~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.52/0.70         <= (~
% 0.52/0.70             ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.70               (u1_struct_0 @ sk_C))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['96', '97'])).
% 0.52/0.70  thf('99', plain,
% 0.52/0.70      (((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['95', '98'])).
% 0.52/0.70  thf('100', plain, ((v1_funct_1 @ sk_D_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('101', plain, ((~ (v1_funct_1 @ sk_D_1)) <= (~ ((v1_funct_1 @ sk_D_1)))),
% 0.52/0.70      inference('split', [status(esa)], ['93'])).
% 0.52/0.70  thf('102', plain, (((v1_funct_1 @ sk_D_1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['100', '101'])).
% 0.52/0.70  thf('103', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70        (k1_zfmisc_1 @ 
% 0.52/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.52/0.70      inference('demod', [status(thm)], ['22', '23'])).
% 0.52/0.70  thf('104', plain,
% 0.52/0.70      (![X6 : $i]:
% 0.52/0.70         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.52/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.70  thf('105', plain,
% 0.52/0.70      ((~ (m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70           (k1_zfmisc_1 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))))
% 0.52/0.70         <= (~
% 0.52/0.70             ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))))),
% 0.52/0.70      inference('split', [status(esa)], ['93'])).
% 0.52/0.70  thf('106', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('107', plain,
% 0.52/0.70      ((~ (m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70           (k1_zfmisc_1 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.52/0.70         <= (~
% 0.52/0.70             ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))))),
% 0.52/0.70      inference('demod', [status(thm)], ['105', '106'])).
% 0.52/0.70  thf('108', plain,
% 0.52/0.70      (((~ (m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70            (k1_zfmisc_1 @ 
% 0.52/0.70             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.52/0.70         | ~ (l1_struct_0 @ sk_B)))
% 0.52/0.70         <= (~
% 0.52/0.70             ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['104', '107'])).
% 0.52/0.70  thf('109', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('110', plain,
% 0.52/0.70      ((~ (m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70           (k1_zfmisc_1 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))
% 0.52/0.70         <= (~
% 0.52/0.70             ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))))),
% 0.52/0.70      inference('demod', [status(thm)], ['108', '109'])).
% 0.52/0.70  thf('111', plain,
% 0.52/0.70      (((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70         (k1_zfmisc_1 @ 
% 0.52/0.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['103', '110'])).
% 0.52/0.70  thf('112', plain,
% 0.52/0.70      (~ ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)) | 
% 0.52/0.70       ~
% 0.52/0.70       ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.70         (k1_zfmisc_1 @ 
% 0.52/0.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))) | 
% 0.52/0.70       ~ ((v1_funct_1 @ sk_D_1)) | 
% 0.52/0.70       ~ ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))),
% 0.52/0.70      inference('split', [status(esa)], ['93'])).
% 0.52/0.70  thf('113', plain, (~ ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C))),
% 0.52/0.70      inference('sat_resolution*', [status(thm)], ['99', '102', '111', '112'])).
% 0.52/0.70  thf('114', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['94', '113'])).
% 0.52/0.70  thf('115', plain,
% 0.52/0.70      (((v3_pre_topc @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ sk_B)
% 0.52/0.70        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('clc', [status(thm)], ['92', '114'])).
% 0.52/0.70  thf('116', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.52/0.70  thf('117', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.52/0.70  thf('118', plain,
% 0.52/0.70      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.52/0.70         ((zip_tseitin_1 @ X13 @ X16 @ X14 @ X17)
% 0.52/0.70          | (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.70  thf('119', plain,
% 0.52/0.70      (![X3 : $i, X4 : $i]:
% 0.52/0.70         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.70  thf('120', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.70         ((zip_tseitin_1 @ X1 @ X3 @ X0 @ X2)
% 0.52/0.70          | (r1_tarski @ X1 @ (u1_struct_0 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['118', '119'])).
% 0.52/0.70  thf('121', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((r1_tarski @ X0 @ (k2_struct_0 @ sk_B))
% 0.52/0.70          | (zip_tseitin_1 @ X0 @ X2 @ sk_C @ X1))),
% 0.52/0.70      inference('sup+', [status(thm)], ['117', '120'])).
% 0.52/0.70  thf('122', plain,
% 0.52/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.70         (~ (zip_tseitin_1 @ (sk_D @ X18 @ X19 @ X20) @ X20 @ X19 @ X18)
% 0.52/0.70          | (v5_pre_topc @ X20 @ X18 @ X19)
% 0.52/0.70          | ~ (zip_tseitin_2 @ X20 @ X19 @ X18))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.70  thf('123', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((r1_tarski @ (sk_D @ X0 @ sk_C @ X1) @ (k2_struct_0 @ sk_B))
% 0.52/0.70          | ~ (zip_tseitin_2 @ X1 @ sk_C @ X0)
% 0.52/0.70          | (v5_pre_topc @ X1 @ X0 @ sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['121', '122'])).
% 0.52/0.70  thf('124', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)
% 0.52/0.70        | (r1_tarski @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ (k2_struct_0 @ sk_B)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['116', '123'])).
% 0.52/0.70  thf('125', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['94', '113'])).
% 0.52/0.70  thf('126', plain,
% 0.52/0.70      (((r1_tarski @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ (k2_struct_0 @ sk_B))
% 0.52/0.70        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('clc', [status(thm)], ['124', '125'])).
% 0.52/0.70  thf('127', plain,
% 0.52/0.70      (![X3 : $i, X5 : $i]:
% 0.52/0.70         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.52/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.70  thf('128', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | (m1_subset_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ 
% 0.52/0.70           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['126', '127'])).
% 0.52/0.70  thf('129', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['6', '13'])).
% 0.52/0.70  thf('130', plain,
% 0.52/0.70      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.52/0.70          | (v3_pre_topc @ 
% 0.52/0.70             (k8_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14) @ X16 @ 
% 0.52/0.70              X13) @ 
% 0.52/0.70             X15)
% 0.52/0.70          | ~ (v3_pre_topc @ X13 @ X14)
% 0.52/0.70          | ~ (zip_tseitin_1 @ X13 @ X16 @ X14 @ X15))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.70  thf('131', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.52/0.70          | ~ (zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1)
% 0.52/0.70          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.52/0.70          | (v3_pre_topc @ 
% 0.52/0.70             (k8_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ X2 @ X0) @ 
% 0.52/0.70             X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['129', '130'])).
% 0.52/0.70  thf('132', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['6', '13'])).
% 0.52/0.70  thf('133', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.52/0.70          | ~ (zip_tseitin_1 @ X0 @ X2 @ sk_B @ X1)
% 0.52/0.70          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.52/0.70          | (v3_pre_topc @ 
% 0.52/0.70             (k8_relset_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ sk_B) @ X2 @ X0) @ 
% 0.52/0.70             X1))),
% 0.52/0.70      inference('demod', [status(thm)], ['131', '132'])).
% 0.52/0.70  thf('134', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70          | (v3_pre_topc @ 
% 0.52/0.70             (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X1 @ 
% 0.52/0.70              (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.52/0.70             X0)
% 0.52/0.70          | ~ (v3_pre_topc @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ sk_B)
% 0.52/0.70          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ X1 @ sk_B @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['128', '133'])).
% 0.52/0.70  thf('135', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ X1 @ sk_B @ X0)
% 0.52/0.70          | (v3_pre_topc @ 
% 0.52/0.70             (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X1 @ 
% 0.52/0.70              (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.52/0.70             X0)
% 0.52/0.70          | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['115', '134'])).
% 0.52/0.70  thf('136', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((v3_pre_topc @ 
% 0.52/0.70           (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X1 @ 
% 0.52/0.70            (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.52/0.70           X0)
% 0.52/0.70          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ X1 @ sk_B @ X0)
% 0.52/0.70          | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['135'])).
% 0.52/0.70  thf('137', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | (v3_pre_topc @ 
% 0.52/0.70           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.52/0.70            sk_D_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.52/0.70           sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['44', '136'])).
% 0.52/0.70  thf('138', plain,
% 0.52/0.70      (((v3_pre_topc @ 
% 0.52/0.70         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_D_1 @ 
% 0.52/0.70          (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.52/0.70         sk_A)
% 0.52/0.70        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['137'])).
% 0.52/0.70  thf('139', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.52/0.70  thf('140', plain,
% 0.52/0.70      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.52/0.70         ((zip_tseitin_1 @ X13 @ X16 @ X14 @ X17)
% 0.52/0.70          | ~ (v3_pre_topc @ 
% 0.52/0.70               (k8_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X14) @ 
% 0.52/0.70                X16 @ X13) @ 
% 0.52/0.70               X17))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.70  thf('141', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (~ (v3_pre_topc @ 
% 0.52/0.70             (k8_relset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B) @ X2 @ X1) @ 
% 0.52/0.70             X0)
% 0.52/0.70          | (zip_tseitin_1 @ X1 @ X2 @ sk_C @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['139', '140'])).
% 0.52/0.70  thf('142', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ sk_D_1 @ sk_C @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['138', '141'])).
% 0.52/0.70  thf('143', plain,
% 0.52/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.70         (~ (zip_tseitin_1 @ (sk_D @ X18 @ X19 @ X20) @ X20 @ X19 @ X18)
% 0.52/0.70          | (v5_pre_topc @ X20 @ X18 @ X19)
% 0.52/0.70          | ~ (zip_tseitin_2 @ X20 @ X19 @ X18))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.70  thf('144', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | ~ (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A)
% 0.52/0.70        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['142', '143'])).
% 0.52/0.70  thf('145', plain,
% 0.52/0.70      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.70        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.52/0.70  thf('146', plain,
% 0.52/0.70      (((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)
% 0.52/0.70        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('clc', [status(thm)], ['144', '145'])).
% 0.52/0.70  thf('147', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['94', '113'])).
% 0.52/0.70  thf('148', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.52/0.70      inference('clc', [status(thm)], ['146', '147'])).
% 0.52/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.70  thf('149', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.70  thf('150', plain, ($false),
% 0.52/0.70      inference('demod', [status(thm)], ['20', '148', '149'])).
% 0.52/0.70  
% 0.52/0.70  % SZS output end Refutation
% 0.52/0.70  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
