%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S6oq3DQVDV

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  268 (5597 expanded)
%              Number of leaves         :   29 (1539 expanded)
%              Depth                    :   44
%              Number of atoms          : 3214 (206788 expanded)
%              Number of equality atoms :    9 (2606 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t66_tmap_1,conjecture,(
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
                                  <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X7 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ~ ( v3_pre_topc @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ sk_E @ sk_B )
      | ~ ( r1_tarski @ sk_E @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_E )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( r1_tarski @ sk_E @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_E )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( r1_tarski @ sk_E @ sk_E )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ~ ( r2_hidden @ sk_G @ sk_E ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ sk_E @ sk_B @ sk_G ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ( r2_hidden @ X4 @ ( sk_D @ X6 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_E @ X0 @ sk_B ) )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_E @ X0 @ sk_B ) )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_G @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('40',plain,
    ( ( r2_hidden @ sk_G @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_hidden @ sk_G @ ( sk_D @ sk_E @ sk_G @ sk_B ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('44',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['29','30'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_E @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_E @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X7 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ~ ( v3_pre_topc @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B )
      | ~ ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['29','30'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ( v3_pre_topc @ ( sk_D @ X6 @ X4 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ sk_E @ X0 @ sk_B ) @ sk_B )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ sk_E @ X0 @ sk_B ) @ sk_B )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( v3_pre_topc @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('69',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_pre_topc @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','72'])).

thf('74',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('82',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('89',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('93',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('94',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_tarski @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_connsp_2 @ X11 @ X8 @ X10 )
      | ( X10 != X12 )
      | ~ ( r1_tmap_1 @ X9 @ X13 @ ( k2_tmap_1 @ X8 @ X13 @ X14 @ X9 ) @ X12 )
      | ( r1_tmap_1 @ X8 @ X13 @ X14 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('95',plain,(
    ! [X8: $i,X9: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ( r1_tmap_1 @ X8 @ X13 @ X14 @ X12 )
      | ~ ( r1_tmap_1 @ X9 @ X13 @ ( k2_tmap_1 @ X8 @ X13 @ X14 @ X9 ) @ X12 )
      | ~ ( m1_connsp_2 @ X11 @ X8 @ X12 )
      | ~ ( r1_tarski @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100','101','102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
        | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference('sup-',[status(thm)],['92','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('107',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
        | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ sk_G )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference('sup-',[status(thm)],['91','108'])).

thf('110',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('111',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['78','79'])).

thf('112',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('113',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ( r1_tarski @ ( sk_D @ X6 @ X4 @ X5 ) @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('120',plain,
    ( ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) ) @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','124'])).

thf('126',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('127',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['29','30'])).

thf('128',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ( r1_tarski @ ( sk_D @ X6 @ X4 @ X5 ) @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r1_tarski @ ( sk_D @ sk_E @ X0 @ sk_B ) @ sk_E )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( sk_D @ sk_E @ X0 @ sk_B ) @ sk_E )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('136',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_E ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_E )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['126','140'])).

thf('142',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('147',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    r1_tarski @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_E @ sk_G @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['125','150'])).

thf('152',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('153',plain,
    ( ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['78','79'])).

thf('156',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('157',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ( r2_hidden @ X4 @ ( sk_D @ X6 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_G @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['155','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('164',plain,
    ( ( r2_hidden @ sk_G @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    r2_hidden @ sk_G @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('168',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('169',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X7 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ~ ( v3_pre_topc @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['78','79'])).

thf('174',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('175',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ( v3_pre_topc @ ( sk_D @ X6 @ X4 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ sk_B )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ X0 @ sk_B ) @ sk_B )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( v3_pre_topc @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['173','179'])).

thf('181',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('182',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['170','171','172','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','185'])).

thf('187',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ sk_G )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['166','188'])).

thf('190',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ sk_G ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    m1_connsp_2 @ ( sk_D @ ( sk_D @ sk_E @ sk_G @ sk_B ) @ sk_G @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(demod,[status(thm)],['109','154','193'])).

thf('195',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['6'])).

thf('196',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['194','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('206',plain,(
    r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ),
    inference('sat_resolution*',[status(thm)],['7','204','205'])).

thf('207',plain,(
    r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ),
    inference(simpl_trail,[status(thm)],['5','206'])).

thf('208',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_tarski @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_connsp_2 @ X11 @ X8 @ X10 )
      | ( X10 != X12 )
      | ~ ( r1_tmap_1 @ X8 @ X13 @ X14 @ X10 )
      | ( r1_tmap_1 @ X9 @ X13 @ ( k2_tmap_1 @ X8 @ X13 @ X14 @ X9 ) @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('211',plain,(
    ! [X8: $i,X9: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ( r1_tmap_1 @ X9 @ X13 @ ( k2_tmap_1 @ X8 @ X13 @ X14 @ X9 ) @ X12 )
      | ~ ( r1_tmap_1 @ X8 @ X13 @ X14 @ X12 )
      | ~ ( m1_connsp_2 @ X11 @ X8 @ X12 )
      | ~ ( r1_tarski @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','211'])).

thf('213',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['212','213','214','215','216','217','218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X1 )
      | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['208','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['207','220'])).

thf('222',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('223',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['29','30'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','224'])).

thf('226',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('230',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['7','204'])).

thf('231',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['228','231'])).

thf('233',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['234','235'])).

thf('237',plain,(
    $false ),
    inference(demod,[status(thm)],['0','236'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S6oq3DQVDV
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 123 iterations in 0.066s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(t66_tmap_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.53                 ( m1_subset_1 @
% 0.20/0.53                   C @ 
% 0.20/0.53                   ( k1_zfmisc_1 @
% 0.20/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( m1_subset_1 @
% 0.20/0.53                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.53                       ( ![F:$i]:
% 0.20/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.53                           ( ![G:$i]:
% 0.20/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.20/0.53                                   ( r2_hidden @ F @ E ) & 
% 0.20/0.53                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.53                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.53                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.53                                   ( r1_tmap_1 @
% 0.20/0.53                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53                ( l1_pre_topc @ B ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                    ( v1_funct_2 @
% 0.20/0.53                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.53                    ( m1_subset_1 @
% 0.20/0.53                      C @ 
% 0.20/0.53                      ( k1_zfmisc_1 @
% 0.20/0.53                        ( k2_zfmisc_1 @
% 0.20/0.53                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.53                  ( ![D:$i]:
% 0.20/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.53                      ( ![E:$i]:
% 0.20/0.53                        ( ( m1_subset_1 @
% 0.20/0.53                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.53                          ( ![F:$i]:
% 0.20/0.53                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.53                              ( ![G:$i]:
% 0.20/0.53                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.20/0.53                                      ( r2_hidden @ F @ E ) & 
% 0.20/0.53                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.53                                      ( ( F ) = ( G ) ) ) =>
% 0.20/0.53                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.53                                      ( r1_tmap_1 @
% 0.20/0.53                                        D @ A @ 
% 0.20/0.53                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.20/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.20/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('4', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.53           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (~
% 0.20/0.53       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) | 
% 0.20/0.53       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.20/0.53      inference('split', [status(esa)], ['6'])).
% 0.20/0.53  thf('8', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t8_connsp_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.53                 ( ?[D:$i]:
% 0.20/0.53                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.20/0.53                     ( v3_pre_topc @ D @ A ) & 
% 0.20/0.53                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.53          | ~ (r2_hidden @ X4 @ X7)
% 0.20/0.53          | ~ (r1_tarski @ X7 @ X6)
% 0.20/0.53          | ~ (v3_pre_topc @ X7 @ X5)
% 0.20/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | ~ (l1_pre_topc @ X5)
% 0.20/0.53          | ~ (v2_pre_topc @ X5)
% 0.20/0.53          | (v2_struct_0 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.20/0.53          | ~ (v3_pre_topc @ sk_E @ sk_B)
% 0.20/0.53          | ~ (r1_tarski @ sk_E @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X1 @ sk_E)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('17', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.20/0.53          | ~ (r1_tarski @ sk_E @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X1 @ sk_E)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_E)
% 0.20/0.53          | ~ (r1_tarski @ sk_E @ sk_E)
% 0.20/0.53          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '18'])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_E)
% 0.20/0.53          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.20/0.53        | ~ (r2_hidden @ sk_G @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '24'])).
% 0.20/0.53  thf('26', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B) | (m1_connsp_2 @ sk_E @ sk_B @ sk_G))),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '28'])).
% 0.20/0.53  thf('30', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.20/0.53      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.53          | ~ (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.53          | (r2_hidden @ X4 @ (sk_D @ X6 @ X4 @ X5))
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | ~ (l1_pre_topc @ X5)
% 0.20/0.53          | ~ (v2_pre_topc @ X5)
% 0.20/0.53          | (v2_struct_0 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | (r2_hidden @ X0 @ (sk_D @ sk_E @ X0 @ sk_B))
% 0.20/0.53          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (r2_hidden @ X0 @ (sk_D @ sk_E @ X0 @ sk_B))
% 0.20/0.53          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (r2_hidden @ sk_G @ (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '37'])).
% 0.20/0.53  thf('39', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (((r2_hidden @ sk_G @ (sk_D @ sk_E @ sk_G @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain, ((r2_hidden @ sk_G @ (sk_D @ sk_E @ sk_G @ sk_B))),
% 0.20/0.53      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.53  thf('44', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.20/0.53      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.53          | ~ (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ X6 @ X4 @ X5) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | ~ (l1_pre_topc @ X5)
% 0.20/0.53          | ~ (v2_pre_topc @ X5)
% 0.20/0.53          | (v2_struct_0 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ sk_E @ X0 @ sk_B) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ sk_E @ X0 @ sk_B) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '50'])).
% 0.20/0.53  thf('52', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      ((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.53          | ~ (r2_hidden @ X4 @ X7)
% 0.20/0.53          | ~ (r1_tarski @ X7 @ X6)
% 0.20/0.53          | ~ (v3_pre_topc @ X7 @ X5)
% 0.20/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | ~ (l1_pre_topc @ X5)
% 0.20/0.53          | ~ (v2_pre_topc @ X5)
% 0.20/0.53          | (v2_struct_0 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.20/0.53          | ~ (v3_pre_topc @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B)
% 0.20/0.53          | ~ (r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X1 @ (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('60', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.20/0.53      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.53          | ~ (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.53          | (v3_pre_topc @ (sk_D @ X6 @ X4 @ X5) @ X5)
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | ~ (l1_pre_topc @ X5)
% 0.20/0.53          | ~ (v2_pre_topc @ X5)
% 0.20/0.53          | (v2_struct_0 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | (v3_pre_topc @ (sk_D @ sk_E @ X0 @ sk_B) @ sk_B)
% 0.20/0.53          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (v3_pre_topc @ (sk_D @ sk_E @ X0 @ sk_B) @ sk_B)
% 0.20/0.53          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v3_pre_topc @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['60', '66'])).
% 0.20/0.53  thf('68', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (((v3_pre_topc @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.53  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('71', plain, ((v3_pre_topc @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B)),
% 0.20/0.53      inference('clc', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.20/0.53          | ~ (r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X1 @ (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['57', '58', '59', '71'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.53          | (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.20/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '72'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.53          | (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)
% 0.20/0.53        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '75'])).
% 0.20/0.53  thf('77', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G))),
% 0.20/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.53  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('80', plain, ((m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)),
% 0.20/0.53      inference('clc', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      ((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.53          | ~ (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ X6 @ X4 @ X5) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | ~ (l1_pre_topc @ X5)
% 0.20/0.53          | ~ (v2_pre_topc @ X5)
% 0.20/0.53          | (v2_struct_0 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.54        | (m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['80', '86'])).
% 0.20/0.54  thf('88', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('89', plain,
% 0.20/0.54      (((m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.54  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('92', plain,
% 0.20/0.54      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))
% 0.20/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('93', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t65_tmap_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.54             ( l1_pre_topc @ B ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.54                 ( m1_subset_1 @
% 0.20/0.54                   C @ 
% 0.20/0.54                   ( k1_zfmisc_1 @
% 0.20/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.54               ( ![D:$i]:
% 0.20/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.54                   ( ![E:$i]:
% 0.20/0.54                     ( ( m1_subset_1 @
% 0.20/0.54                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.54                       ( ![F:$i]:
% 0.20/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.54                           ( ![G:$i]:
% 0.20/0.54                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.54                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.54                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.20/0.54                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.54                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.54                                   ( r1_tmap_1 @
% 0.20/0.54                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X8)
% 0.20/0.54          | ~ (v2_pre_topc @ X8)
% 0.20/0.54          | ~ (l1_pre_topc @ X8)
% 0.20/0.54          | (v2_struct_0 @ X9)
% 0.20/0.54          | ~ (m1_pre_topc @ X9 @ X8)
% 0.20/0.54          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.54          | ~ (r1_tarski @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.54          | ~ (m1_connsp_2 @ X11 @ X8 @ X10)
% 0.20/0.54          | ((X10) != (X12))
% 0.20/0.54          | ~ (r1_tmap_1 @ X9 @ X13 @ (k2_tmap_1 @ X8 @ X13 @ X14 @ X9) @ X12)
% 0.20/0.54          | (r1_tmap_1 @ X8 @ X13 @ X14 @ X10)
% 0.20/0.54          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.54               (k1_zfmisc_1 @ 
% 0.20/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))))
% 0.20/0.54          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))
% 0.20/0.54          | ~ (v1_funct_1 @ X14)
% 0.20/0.54          | ~ (l1_pre_topc @ X13)
% 0.20/0.54          | ~ (v2_pre_topc @ X13)
% 0.20/0.54          | (v2_struct_0 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.54  thf('95', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X13)
% 0.20/0.54          | ~ (v2_pre_topc @ X13)
% 0.20/0.54          | ~ (l1_pre_topc @ X13)
% 0.20/0.54          | ~ (v1_funct_1 @ X14)
% 0.20/0.54          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.54               (k1_zfmisc_1 @ 
% 0.20/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))))
% 0.20/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.54          | (r1_tmap_1 @ X8 @ X13 @ X14 @ X12)
% 0.20/0.54          | ~ (r1_tmap_1 @ X9 @ X13 @ (k2_tmap_1 @ X8 @ X13 @ X14 @ X9) @ X12)
% 0.20/0.54          | ~ (m1_connsp_2 @ X11 @ X8 @ X12)
% 0.20/0.54          | ~ (r1_tarski @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.54          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X8))
% 0.20/0.54          | ~ (m1_pre_topc @ X9 @ X8)
% 0.20/0.54          | (v2_struct_0 @ X9)
% 0.20/0.54          | ~ (l1_pre_topc @ X8)
% 0.20/0.54          | ~ (v2_pre_topc @ X8)
% 0.20/0.54          | (v2_struct_0 @ X8))),
% 0.20/0.54      inference('simplify', [status(thm)], ['94'])).
% 0.20/0.54  thf('96', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.54          | (v2_struct_0 @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.20/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54               (u1_struct_0 @ sk_A))
% 0.20/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['93', '95'])).
% 0.20/0.54  thf('97', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('100', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('103', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | (v2_struct_0 @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.20/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)],
% 0.20/0.54                ['96', '97', '98', '99', '100', '101', '102'])).
% 0.20/0.54  thf('104', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          ((v2_struct_0 @ sk_A)
% 0.20/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))
% 0.20/0.54           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.20/0.54           | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.20/0.54           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.54           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.54           | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.20/0.54           | (v2_struct_0 @ sk_D_1)
% 0.20/0.54           | (v2_struct_0 @ sk_B)))
% 0.20/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['92', '103'])).
% 0.20/0.54  thf('105', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('106', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('107', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('108', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          ((v2_struct_0 @ sk_A)
% 0.20/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.20/0.54           | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.20/0.54           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.54           | (v2_struct_0 @ sk_D_1)
% 0.20/0.54           | (v2_struct_0 @ sk_B)))
% 0.20/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.20/0.54      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.20/0.54  thf('109', plain,
% 0.20/0.54      ((((v2_struct_0 @ sk_B)
% 0.20/0.54         | (v2_struct_0 @ sk_D_1)
% 0.20/0.54         | ~ (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54              (u1_struct_0 @ sk_D_1))
% 0.20/0.54         | ~ (m1_connsp_2 @ 
% 0.20/0.54              (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ sk_B @ sk_G)
% 0.20/0.54         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.20/0.54         | (v2_struct_0 @ sk_A)))
% 0.20/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['91', '108'])).
% 0.20/0.54  thf('110', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('111', plain,
% 0.20/0.54      ((m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)),
% 0.20/0.54      inference('clc', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('112', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('113', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.54          | ~ (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.54          | (r1_tarski @ (sk_D @ X6 @ X4 @ X5) @ X6)
% 0.20/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.54          | ~ (l1_pre_topc @ X5)
% 0.20/0.54          | ~ (v2_pre_topc @ X5)
% 0.20/0.54          | (v2_struct_0 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.54  thf('114', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.54          | (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.20/0.54             (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.54          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['112', '113'])).
% 0.20/0.54  thf('115', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('117', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.20/0.54             (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.54          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.20/0.54  thf('118', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.54        | (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54           (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['111', '117'])).
% 0.20/0.54  thf('119', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('120', plain,
% 0.20/0.54      (((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54         (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['118', '119'])).
% 0.20/0.54  thf('121', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('122', plain,
% 0.20/0.54      ((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54        (sk_D @ sk_E @ sk_G @ sk_B))),
% 0.20/0.54      inference('clc', [status(thm)], ['120', '121'])).
% 0.20/0.54  thf('123', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('124', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ 
% 0.20/0.54               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['122', '123'])).
% 0.20/0.54  thf('125', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ X0)
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_C @ X0 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B)) @ 
% 0.20/0.54             (sk_D @ sk_E @ sk_G @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['110', '124'])).
% 0.20/0.54  thf('126', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('127', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.20/0.54      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('128', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('129', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.54          | ~ (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.54          | (r1_tarski @ (sk_D @ X6 @ X4 @ X5) @ X6)
% 0.20/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.54          | ~ (l1_pre_topc @ X5)
% 0.20/0.54          | ~ (v2_pre_topc @ X5)
% 0.20/0.54          | (v2_struct_0 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.54  thf('130', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.54          | (r1_tarski @ (sk_D @ sk_E @ X0 @ sk_B) @ sk_E)
% 0.20/0.54          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['128', '129'])).
% 0.20/0.54  thf('131', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('132', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('133', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | (r1_tarski @ (sk_D @ sk_E @ X0 @ sk_B) @ sk_E)
% 0.20/0.54          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.20/0.54  thf('134', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.54        | (r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_E)
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['127', '133'])).
% 0.20/0.54  thf('135', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('136', plain,
% 0.20/0.54      (((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_E) | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['134', '135'])).
% 0.20/0.54  thf('137', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('138', plain, ((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_E)),
% 0.20/0.54      inference('clc', [status(thm)], ['136', '137'])).
% 0.20/0.54  thf('139', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('140', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ sk_E)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['138', '139'])).
% 0.20/0.54  thf('141', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0)
% 0.20/0.54          | (r2_hidden @ (sk_C @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B)) @ sk_E))),
% 0.20/0.54      inference('sup-', [status(thm)], ['126', '140'])).
% 0.20/0.54  thf('142', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('143', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('144', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.20/0.54      inference('sup-', [status(thm)], ['142', '143'])).
% 0.20/0.54  thf('145', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0)
% 0.20/0.54          | (r2_hidden @ (sk_C @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B)) @ 
% 0.20/0.54             (u1_struct_0 @ sk_D_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['141', '144'])).
% 0.20/0.54  thf('146', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('147', plain,
% 0.20/0.54      (((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.20/0.54        | (r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['145', '146'])).
% 0.20/0.54  thf('148', plain,
% 0.20/0.54      ((r1_tarski @ (sk_D @ sk_E @ sk_G @ sk_B) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.54      inference('simplify', [status(thm)], ['147'])).
% 0.20/0.54  thf('149', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('150', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (sk_D @ sk_E @ sk_G @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['148', '149'])).
% 0.20/0.54  thf('151', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ X0)
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_C @ X0 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B)) @ 
% 0.20/0.54             (u1_struct_0 @ sk_D_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['125', '150'])).
% 0.20/0.54  thf('152', plain,
% 0.20/0.54      (![X1 : $i, X3 : $i]:
% 0.20/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('153', plain,
% 0.20/0.54      (((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54         (u1_struct_0 @ sk_D_1))
% 0.20/0.54        | (r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54           (u1_struct_0 @ sk_D_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['151', '152'])).
% 0.20/0.54  thf('154', plain,
% 0.20/0.54      ((r1_tarski @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54        (u1_struct_0 @ sk_D_1))),
% 0.20/0.54      inference('simplify', [status(thm)], ['153'])).
% 0.20/0.54  thf('155', plain,
% 0.20/0.54      ((m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)),
% 0.20/0.54      inference('clc', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('156', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('157', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.54          | ~ (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.54          | (r2_hidden @ X4 @ (sk_D @ X6 @ X4 @ X5))
% 0.20/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.54          | ~ (l1_pre_topc @ X5)
% 0.20/0.54          | ~ (v2_pre_topc @ X5)
% 0.20/0.54          | (v2_struct_0 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.54  thf('158', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.54          | (r2_hidden @ X0 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B))
% 0.20/0.54          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['156', '157'])).
% 0.20/0.54  thf('159', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('160', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('161', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | (r2_hidden @ X0 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B))
% 0.20/0.54          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.20/0.54  thf('162', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.54        | (r2_hidden @ sk_G @ 
% 0.20/0.54           (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B))
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['155', '161'])).
% 0.20/0.54  thf('163', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('164', plain,
% 0.20/0.54      (((r2_hidden @ sk_G @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B))
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['162', '163'])).
% 0.20/0.54  thf('165', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('166', plain,
% 0.20/0.54      ((r2_hidden @ sk_G @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B))),
% 0.20/0.54      inference('clc', [status(thm)], ['164', '165'])).
% 0.20/0.54  thf('167', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.54  thf('168', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('169', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.54          | ~ (r2_hidden @ X4 @ X7)
% 0.20/0.54          | ~ (r1_tarski @ X7 @ X6)
% 0.20/0.54          | ~ (v3_pre_topc @ X7 @ X5)
% 0.20/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.54          | (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.54          | ~ (l1_pre_topc @ X5)
% 0.20/0.54          | ~ (v2_pre_topc @ X5)
% 0.20/0.54          | (v2_struct_0 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.54  thf('170', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.20/0.54          | ~ (v3_pre_topc @ 
% 0.20/0.54               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ sk_B)
% 0.20/0.54          | ~ (r1_tarski @ 
% 0.20/0.54               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X1 @ 
% 0.20/0.54               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B))
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['168', '169'])).
% 0.20/0.54  thf('171', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('172', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('173', plain,
% 0.20/0.54      ((m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ sk_G)),
% 0.20/0.54      inference('clc', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('174', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ sk_E @ sk_G @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('175', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.54          | ~ (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.54          | (v3_pre_topc @ (sk_D @ X6 @ X4 @ X5) @ X5)
% 0.20/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.54          | ~ (l1_pre_topc @ X5)
% 0.20/0.54          | ~ (v2_pre_topc @ X5)
% 0.20/0.54          | (v2_struct_0 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.54  thf('176', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.54          | (v3_pre_topc @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.20/0.54             sk_B)
% 0.20/0.54          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['174', '175'])).
% 0.20/0.54  thf('177', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('178', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('179', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | (v3_pre_topc @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ X0 @ sk_B) @ 
% 0.20/0.54             sk_B)
% 0.20/0.54          | ~ (m1_connsp_2 @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.20/0.54  thf('180', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.54        | (v3_pre_topc @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54           sk_B)
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['173', '179'])).
% 0.20/0.54  thf('181', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('182', plain,
% 0.20/0.54      (((v3_pre_topc @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54         sk_B)
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['180', '181'])).
% 0.20/0.54  thf('183', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('184', plain,
% 0.20/0.54      ((v3_pre_topc @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ sk_B)),
% 0.20/0.54      inference('clc', [status(thm)], ['182', '183'])).
% 0.20/0.54  thf('185', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.20/0.54          | ~ (r1_tarski @ 
% 0.20/0.54               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X1 @ 
% 0.20/0.54               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B))
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['170', '171', '172', '184'])).
% 0.20/0.54  thf('186', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ 
% 0.20/0.54               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B))
% 0.20/0.54          | (m1_connsp_2 @ 
% 0.20/0.54             (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ 
% 0.20/0.54               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54          | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['167', '185'])).
% 0.20/0.54  thf('187', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('188', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ 
% 0.20/0.54               (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B))
% 0.20/0.54          | (m1_connsp_2 @ 
% 0.20/0.54             (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ sk_B @ X0)
% 0.20/0.54          | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['186', '187'])).
% 0.20/0.54  thf('189', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B)
% 0.20/0.54        | (m1_connsp_2 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54           sk_B @ sk_G)
% 0.20/0.54        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['166', '188'])).
% 0.20/0.54  thf('190', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('191', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B)
% 0.20/0.54        | (m1_connsp_2 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54           sk_B @ sk_G))),
% 0.20/0.54      inference('demod', [status(thm)], ['189', '190'])).
% 0.20/0.54  thf('192', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('193', plain,
% 0.20/0.54      ((m1_connsp_2 @ (sk_D @ (sk_D @ sk_E @ sk_G @ sk_B) @ sk_G @ sk_B) @ 
% 0.20/0.54        sk_B @ sk_G)),
% 0.20/0.54      inference('clc', [status(thm)], ['191', '192'])).
% 0.20/0.54  thf('194', plain,
% 0.20/0.54      ((((v2_struct_0 @ sk_B)
% 0.20/0.54         | (v2_struct_0 @ sk_D_1)
% 0.20/0.54         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.20/0.54         | (v2_struct_0 @ sk_A)))
% 0.20/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.20/0.54      inference('demod', [status(thm)], ['109', '154', '193'])).
% 0.20/0.54  thf('195', plain,
% 0.20/0.54      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.20/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.20/0.54      inference('split', [status(esa)], ['6'])).
% 0.20/0.54  thf('196', plain, (((sk_F) = (sk_G))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('197', plain,
% 0.20/0.54      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.20/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.20/0.54      inference('demod', [status(thm)], ['195', '196'])).
% 0.20/0.54  thf('198', plain,
% 0.20/0.54      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.20/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)) & 
% 0.20/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['194', '197'])).
% 0.20/0.54  thf('199', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('200', plain,
% 0.20/0.54      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.20/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)) & 
% 0.20/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.20/0.54      inference('clc', [status(thm)], ['198', '199'])).
% 0.20/0.54  thf('201', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('202', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_D_1))
% 0.20/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)) & 
% 0.20/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.20/0.54      inference('clc', [status(thm)], ['200', '201'])).
% 0.20/0.54  thf('203', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('204', plain,
% 0.20/0.54      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)) | 
% 0.20/0.54       ~
% 0.20/0.54       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))),
% 0.20/0.54      inference('sup-', [status(thm)], ['202', '203'])).
% 0.20/0.54  thf('205', plain,
% 0.20/0.54      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)) | 
% 0.20/0.54       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('206', plain, (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['7', '204', '205'])).
% 0.20/0.54  thf('207', plain, ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['5', '206'])).
% 0.20/0.54  thf('208', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('209', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('210', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X8)
% 0.20/0.54          | ~ (v2_pre_topc @ X8)
% 0.20/0.54          | ~ (l1_pre_topc @ X8)
% 0.20/0.54          | (v2_struct_0 @ X9)
% 0.20/0.54          | ~ (m1_pre_topc @ X9 @ X8)
% 0.20/0.54          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.54          | ~ (r1_tarski @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.54          | ~ (m1_connsp_2 @ X11 @ X8 @ X10)
% 0.20/0.54          | ((X10) != (X12))
% 0.20/0.54          | ~ (r1_tmap_1 @ X8 @ X13 @ X14 @ X10)
% 0.20/0.54          | (r1_tmap_1 @ X9 @ X13 @ (k2_tmap_1 @ X8 @ X13 @ X14 @ X9) @ X12)
% 0.20/0.54          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.54               (k1_zfmisc_1 @ 
% 0.20/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))))
% 0.20/0.54          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))
% 0.20/0.54          | ~ (v1_funct_1 @ X14)
% 0.20/0.54          | ~ (l1_pre_topc @ X13)
% 0.20/0.54          | ~ (v2_pre_topc @ X13)
% 0.20/0.54          | (v2_struct_0 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.54  thf('211', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X13)
% 0.20/0.54          | ~ (v2_pre_topc @ X13)
% 0.20/0.54          | ~ (l1_pre_topc @ X13)
% 0.20/0.54          | ~ (v1_funct_1 @ X14)
% 0.20/0.54          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.54               (k1_zfmisc_1 @ 
% 0.20/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))))
% 0.20/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.54          | (r1_tmap_1 @ X9 @ X13 @ (k2_tmap_1 @ X8 @ X13 @ X14 @ X9) @ X12)
% 0.20/0.54          | ~ (r1_tmap_1 @ X8 @ X13 @ X14 @ X12)
% 0.20/0.54          | ~ (m1_connsp_2 @ X11 @ X8 @ X12)
% 0.20/0.54          | ~ (r1_tarski @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.54          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X8))
% 0.20/0.54          | ~ (m1_pre_topc @ X9 @ X8)
% 0.20/0.54          | (v2_struct_0 @ X9)
% 0.20/0.54          | ~ (l1_pre_topc @ X8)
% 0.20/0.54          | ~ (v2_pre_topc @ X8)
% 0.20/0.54          | (v2_struct_0 @ X8))),
% 0.20/0.54      inference('simplify', [status(thm)], ['210'])).
% 0.20/0.54  thf('212', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.54          | (v2_struct_0 @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.54          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.20/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.20/0.54             X1)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54               (u1_struct_0 @ sk_A))
% 0.20/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['209', '211'])).
% 0.20/0.54  thf('213', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('214', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('215', plain,
% 0.20/0.54      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('216', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('218', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('219', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | (v2_struct_0 @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.54          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.20/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.20/0.54             X1)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)],
% 0.20/0.54                ['212', '213', '214', '215', '216', '217', '218'])).
% 0.20/0.54  thf('220', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.20/0.54             X1)
% 0.20/0.54          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.20/0.54          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X1)
% 0.20/0.54          | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.54          | (v2_struct_0 @ X0)
% 0.20/0.54          | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['208', '219'])).
% 0.20/0.54  thf('221', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | (v2_struct_0 @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.54          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.20/0.54          | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.20/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.20/0.54             sk_G)
% 0.20/0.54          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['207', '220'])).
% 0.20/0.54  thf('222', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('223', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.20/0.54      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('224', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | (v2_struct_0 @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.54          | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.20/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.20/0.54             sk_G)
% 0.20/0.54          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['221', '222', '223'])).
% 0.20/0.54  thf('225', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))
% 0.20/0.54        | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.20/0.54        | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.20/0.54        | (v2_struct_0 @ sk_D_1)
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '224'])).
% 0.20/0.54  thf('226', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('227', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('228', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.20/0.54        | (v2_struct_0 @ sk_D_1)
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.20/0.54  thf('229', plain,
% 0.20/0.54      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))
% 0.20/0.54         <= (~
% 0.20/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.20/0.54      inference('split', [status(esa)], ['6'])).
% 0.20/0.54  thf('230', plain,
% 0.20/0.54      (~
% 0.20/0.54       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['7', '204'])).
% 0.20/0.54  thf('231', plain,
% 0.20/0.54      (~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.54          (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['229', '230'])).
% 0.20/0.54  thf('232', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['228', '231'])).
% 0.20/0.54  thf('233', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('234', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['232', '233'])).
% 0.20/0.54  thf('235', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('236', plain, ((v2_struct_0 @ sk_D_1)),
% 0.20/0.54      inference('clc', [status(thm)], ['234', '235'])).
% 0.20/0.54  thf('237', plain, ($false), inference('demod', [status(thm)], ['0', '236'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
