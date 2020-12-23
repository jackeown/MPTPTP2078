%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qdd2ZyZ0F6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:07 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 266 expanded)
%              Number of leaves         :   25 (  88 expanded)
%              Depth                    :   29
%              Number of atoms          : 1832 (8162 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t78_tmap_1,conjecture,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

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
                       => ( ( m1_pre_topc @ C @ D )
                         => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X8 @ X9 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X8 @ X9 @ X7 @ X10 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X8 @ X9 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

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

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 )
      | ( X0 != X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_funct_2 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t77_tmap_1,axiom,(
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
                         => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ F @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                              & ( m1_pre_topc @ D @ C ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) @ ( k3_tmap_1 @ X13 @ X11 @ X15 @ X12 @ X14 ) @ ( k2_tmap_1 @ X13 @ X11 @ X16 @ X12 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X11 ) @ X14 @ ( k2_tmap_1 @ X13 @ X11 @ X16 @ X15 ) )
      | ~ ( m1_pre_topc @ X12 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('75',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qdd2ZyZ0F6
% 0.16/0.37  % Computer   : n014.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:45:52 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 116 iterations in 0.129s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.61  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.38/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.61  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.38/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.38/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.61  thf(t78_tmap_1, conjecture,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.61             ( l1_pre_topc @ B ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.61               ( ![D:$i]:
% 0.38/0.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.61                   ( ![E:$i]:
% 0.38/0.61                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.61                         ( v1_funct_2 @
% 0.38/0.61                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.61                         ( m1_subset_1 @
% 0.38/0.61                           E @ 
% 0.38/0.61                           ( k1_zfmisc_1 @
% 0.38/0.61                             ( k2_zfmisc_1 @
% 0.38/0.61                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.61                       ( ( m1_pre_topc @ C @ D ) =>
% 0.38/0.61                         ( r2_funct_2 @
% 0.38/0.61                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.61                           ( k3_tmap_1 @
% 0.38/0.61                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.38/0.61                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i]:
% 0.38/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.61            ( l1_pre_topc @ A ) ) =>
% 0.38/0.61          ( ![B:$i]:
% 0.38/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.61                ( l1_pre_topc @ B ) ) =>
% 0.38/0.61              ( ![C:$i]:
% 0.38/0.61                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.61                  ( ![D:$i]:
% 0.38/0.61                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.61                      ( ![E:$i]:
% 0.38/0.61                        ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.61                            ( v1_funct_2 @
% 0.38/0.61                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.61                            ( m1_subset_1 @
% 0.38/0.61                              E @ 
% 0.38/0.61                              ( k1_zfmisc_1 @
% 0.38/0.61                                ( k2_zfmisc_1 @
% 0.38/0.61                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.61                          ( ( m1_pre_topc @ C @ D ) =>
% 0.38/0.61                            ( r2_funct_2 @
% 0.38/0.61                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.61                              ( k3_tmap_1 @
% 0.38/0.61                                A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.38/0.61                              ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t78_tmap_1])).
% 0.38/0.61  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(dt_l1_pre_topc, axiom,
% 0.38/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.61  thf('2', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('3', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('4', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('5', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_E @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(dt_k2_tmap_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.38/0.61         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.61         ( m1_subset_1 @
% 0.38/0.61           C @ 
% 0.38/0.61           ( k1_zfmisc_1 @
% 0.38/0.61             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.38/0.61         ( l1_struct_0 @ D ) ) =>
% 0.38/0.61       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.38/0.61         ( v1_funct_2 @
% 0.38/0.61           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.38/0.61           ( u1_struct_0 @ B ) ) & 
% 0.38/0.61         ( m1_subset_1 @
% 0.38/0.61           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.38/0.61           ( k1_zfmisc_1 @
% 0.38/0.61             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X7 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X7)
% 0.38/0.61          | ~ (l1_struct_0 @ X9)
% 0.38/0.61          | ~ (l1_struct_0 @ X8)
% 0.38/0.61          | ~ (l1_struct_0 @ X10)
% 0.38/0.61          | (v1_funct_1 @ (k2_tmap_1 @ X8 @ X9 @ X7 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_B)
% 0.38/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.61  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_B)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['5', '11'])).
% 0.38/0.61  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ sk_B)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ sk_B)
% 0.38/0.61          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['4', '14'])).
% 0.38/0.61  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.61  thf('18', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('19', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_E @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X7 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X7)
% 0.38/0.61          | ~ (l1_struct_0 @ X9)
% 0.38/0.61          | ~ (l1_struct_0 @ X8)
% 0.38/0.61          | ~ (l1_struct_0 @ X10)
% 0.38/0.61          | (v1_funct_2 @ (k2_tmap_1 @ X8 @ X9 @ X7 @ X10) @ 
% 0.38/0.61             (u1_struct_0 @ X10) @ (u1_struct_0 @ X9)))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_B)
% 0.38/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('23', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_B)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.38/0.61  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ sk_B)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ sk_B)
% 0.38/0.61          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['18', '28'])).
% 0.38/0.61  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.61  thf('33', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('34', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_E @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X7 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X7)
% 0.38/0.61          | ~ (l1_struct_0 @ X9)
% 0.38/0.61          | ~ (l1_struct_0 @ X8)
% 0.38/0.61          | ~ (l1_struct_0 @ X10)
% 0.38/0.61          | (m1_subset_1 @ (k2_tmap_1 @ X8 @ X9 @ X7 @ X10) @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9)))))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61           (k1_zfmisc_1 @ 
% 0.38/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_B)
% 0.38/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.61  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61           (k1_zfmisc_1 @ 
% 0.38/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.38/0.61  thf('41', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ sk_B)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['34', '40'])).
% 0.38/0.61  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ sk_B)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.38/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.61  thf('44', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ sk_B)
% 0.38/0.61          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['33', '43'])).
% 0.38/0.61  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61           (k1_zfmisc_1 @ 
% 0.38/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.61  thf(redefinition_r2_funct_2, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.61         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.61       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.38/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X3)
% 0.38/0.61          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.38/0.61          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.38/0.61          | (r2_funct_2 @ X1 @ X2 @ X0 @ X3)
% 0.38/0.61          | ((X0) != (X3)))),
% 0.38/0.61      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.38/0.61  thf('48', plain,
% 0.38/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.61         ((r2_funct_2 @ X1 @ X2 @ X3 @ X3)
% 0.38/0.61          | ~ (v1_funct_1 @ X3)
% 0.38/0.61          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.38/0.61          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.38/0.61      inference('simplify', [status(thm)], ['47'])).
% 0.38/0.61  thf('49', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['46', '48'])).
% 0.38/0.61  thf('50', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['32', '49'])).
% 0.38/0.61  thf('51', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['50'])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.61  thf('53', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))),
% 0.38/0.61      inference('clc', [status(thm)], ['51', '52'])).
% 0.38/0.61  thf('54', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61           (k1_zfmisc_1 @ 
% 0.38/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.61  thf(t77_tmap_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.61             ( l1_pre_topc @ B ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.61               ( ![D:$i]:
% 0.38/0.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.61                   ( ![E:$i]:
% 0.38/0.61                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.61                         ( v1_funct_2 @
% 0.38/0.61                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.61                         ( m1_subset_1 @
% 0.38/0.61                           E @ 
% 0.38/0.61                           ( k1_zfmisc_1 @
% 0.38/0.61                             ( k2_zfmisc_1 @
% 0.38/0.61                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.61                       ( ![F:$i]:
% 0.38/0.61                         ( ( ( v1_funct_1 @ F ) & 
% 0.38/0.61                             ( v1_funct_2 @
% 0.38/0.61                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.61                             ( m1_subset_1 @
% 0.38/0.61                               F @ 
% 0.38/0.61                               ( k1_zfmisc_1 @
% 0.38/0.61                                 ( k2_zfmisc_1 @
% 0.38/0.61                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.61                           ( ( ( r2_funct_2 @
% 0.38/0.61                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.61                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.38/0.61                               ( m1_pre_topc @ D @ C ) ) =>
% 0.38/0.61                             ( r2_funct_2 @
% 0.38/0.61                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.61                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 0.38/0.61                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf('55', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X12)
% 0.38/0.61          | ~ (m1_pre_topc @ X12 @ X13)
% 0.38/0.61          | ~ (v1_funct_1 @ X14)
% 0.38/0.61          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X11))
% 0.38/0.61          | ~ (m1_subset_1 @ X14 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X11))))
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ 
% 0.38/0.61             (k3_tmap_1 @ X13 @ X11 @ X15 @ X12 @ X14) @ 
% 0.38/0.61             (k2_tmap_1 @ X13 @ X11 @ X16 @ X12))
% 0.38/0.61          | ~ (r2_funct_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X11) @ X14 @ 
% 0.38/0.61               (k2_tmap_1 @ X13 @ X11 @ X16 @ X15))
% 0.38/0.61          | ~ (m1_pre_topc @ X12 @ X15)
% 0.38/0.61          | ~ (m1_subset_1 @ X16 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.38/0.61          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.38/0.61          | ~ (v1_funct_1 @ X16)
% 0.38/0.61          | ~ (m1_pre_topc @ X15 @ X13)
% 0.38/0.61          | (v2_struct_0 @ X15)
% 0.38/0.61          | ~ (l1_pre_topc @ X13)
% 0.38/0.61          | ~ (v2_pre_topc @ X13)
% 0.38/0.61          | (v2_struct_0 @ X13))),
% 0.38/0.61      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.38/0.61  thf('56', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | ~ (v2_pre_topc @ X1)
% 0.38/0.61          | ~ (l1_pre_topc @ X1)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ X1)
% 0.38/0.61          | ~ (v1_funct_1 @ X2)
% 0.38/0.61          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (m1_subset_1 @ X2 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (m1_pre_topc @ X3 @ X0)
% 0.38/0.61          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61               (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.38/0.61             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X3))
% 0.38/0.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (m1_pre_topc @ X3 @ X1)
% 0.38/0.61          | (v2_struct_0 @ X3)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.61  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('58', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('59', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | ~ (v2_pre_topc @ X1)
% 0.38/0.61          | ~ (l1_pre_topc @ X1)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ X1)
% 0.38/0.61          | ~ (v1_funct_1 @ X2)
% 0.38/0.61          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (m1_subset_1 @ X2 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (m1_pre_topc @ X3 @ X0)
% 0.38/0.61          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61               (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.38/0.61             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X3))
% 0.38/0.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (m1_pre_topc @ X3 @ X1)
% 0.38/0.61          | (v2_struct_0 @ X3)
% 0.38/0.61          | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.38/0.61  thf('60', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ sk_E @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['53', '59'])).
% 0.38/0.61  thf('61', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_E @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('62', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('63', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('66', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['60', '61', '62', '63', '64', '65'])).
% 0.38/0.61  thf('67', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 0.38/0.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.38/0.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | (v2_struct_0 @ sk_B)
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['66'])).
% 0.38/0.61  thf('68', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['31', '67'])).
% 0.38/0.61  thf('69', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | (v2_struct_0 @ sk_B)
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['68'])).
% 0.38/0.61  thf('70', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '69'])).
% 0.38/0.61  thf('71', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | (v2_struct_0 @ sk_B)
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['70'])).
% 0.38/0.61  thf('72', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['3', '71'])).
% 0.38/0.61  thf('73', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['2', '72'])).
% 0.38/0.61  thf('74', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(dt_m1_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.61  thf('75', plain,
% 0.38/0.61      (![X5 : $i, X6 : $i]:
% 0.38/0.61         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.61  thf('76', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.38/0.61      inference('sup-', [status(thm)], ['74', '75'])).
% 0.38/0.61  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('78', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.61      inference('demod', [status(thm)], ['76', '77'])).
% 0.38/0.61  thf('79', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.38/0.61          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.38/0.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.38/0.61             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.38/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['73', '78'])).
% 0.38/0.61  thf('80', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_C)
% 0.38/0.61        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.61        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.38/0.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.38/0.61           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '79'])).
% 0.38/0.61  thf('81', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('82', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_C)
% 0.38/0.61        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.38/0.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.38/0.61           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['80', '81'])).
% 0.38/0.61  thf('83', plain,
% 0.38/0.61      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.61          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.38/0.61           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.38/0.61          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('84', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v2_struct_0 @ sk_C)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.38/0.61  thf('85', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('86', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['84', '85'])).
% 0.38/0.61  thf('87', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('88', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.38/0.61      inference('clc', [status(thm)], ['86', '87'])).
% 0.38/0.61  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('90', plain, ((v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('clc', [status(thm)], ['88', '89'])).
% 0.38/0.61  thf('91', plain, ($false), inference('demod', [status(thm)], ['0', '90'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
