%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MDc9JgYynT

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 653 expanded)
%              Number of leaves         :   29 ( 194 expanded)
%              Depth                    :   28
%              Number of atoms          : 1946 (25240 expanded)
%              Number of equality atoms :   11 ( 325 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ C )
                            & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ sk_G @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['22'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( r1_tarski @ ( sk_D @ X6 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_E @ sk_B ) @ sk_E )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_E @ sk_B ) @ sk_E ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_E )
    | ~ ( r2_hidden @ sk_G @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['12','13'])).

thf('35',plain,
    ( ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_E ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_E )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_G @ sk_E @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ sk_G @ sk_E @ sk_B ) ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['24','39'])).

thf('41',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D @ sk_G @ sk_E @ sk_B ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,
    ( ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( m1_connsp_2 @ ( sk_D @ X6 @ X4 @ X5 ) @ X5 @ X6 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_E @ sk_B ) @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_E @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ sk_G )
    | ~ ( r2_hidden @ sk_G @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['12','13'])).

thf('62',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('67',plain,(
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

thf('68',plain,(
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
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ X1 )
      | ~ ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ sk_G )
        | ~ ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference('sup-',[status(thm)],['51','80'])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference('sup-',[status(thm)],['47','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference(split,[status(esa)],['50'])).

thf('96',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['23','94','95'])).

thf('97',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['19','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
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

thf('100',plain,(
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
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('112',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','113'])).

thf('115',plain,(
    r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('116',plain,(
    m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['62','63'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F ) ),
    inference(split,[status(esa)],['86'])).

thf('119',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('122',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference(split,[status(esa)],['22'])).

thf('125',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['23','94','125'])).

thf('127',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['120','126'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['117','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['0','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MDc9JgYynT
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:13:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 95 iterations in 0.059s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(t66_tmap_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                 ( m1_subset_1 @
% 0.20/0.50                   C @ 
% 0.20/0.50                   ( k1_zfmisc_1 @
% 0.20/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( m1_subset_1 @
% 0.20/0.50                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.50                       ( ![F:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                           ( ![G:$i]:
% 0.20/0.50                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.20/0.50                                   ( r2_hidden @ F @ E ) & 
% 0.20/0.50                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.50                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.50                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.50                                   ( r1_tmap_1 @
% 0.20/0.50                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50                ( l1_pre_topc @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                    ( v1_funct_2 @
% 0.20/0.50                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                    ( m1_subset_1 @
% 0.20/0.50                      C @ 
% 0.20/0.50                      ( k1_zfmisc_1 @
% 0.20/0.50                        ( k2_zfmisc_1 @
% 0.20/0.50                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                      ( ![E:$i]:
% 0.20/0.50                        ( ( m1_subset_1 @
% 0.20/0.50                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.50                          ( ![F:$i]:
% 0.20/0.50                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                              ( ![G:$i]:
% 0.20/0.50                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.20/0.50                                      ( r2_hidden @ F @ E ) & 
% 0.20/0.50                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.50                                      ( ( F ) = ( G ) ) ) =>
% 0.20/0.50                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.50                                      ( r1_tmap_1 @
% 0.20/0.50                                        D @ A @ 
% 0.20/0.50                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t9_connsp_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.50             ( ![C:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.50                      ( ![D:$i]:
% 0.20/0.50                        ( ( m1_subset_1 @
% 0.20/0.50                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.20/0.50                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.50          | ~ (v3_pre_topc @ X4 @ X5)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X6 @ X4 @ X5) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.50          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (l1_pre_topc @ X5)
% 0.20/0.50          | ~ (v2_pre_topc @ X5)
% 0.20/0.50          | (v2_struct_0 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_E)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X0 @ sk_E @ sk_B) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.50          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_E)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X0 @ sk_E @ sk_B) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (((m1_subset_1 @ (sk_D @ sk_G @ sk_E @ sk_B) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.50        | ~ (r2_hidden @ sk_G @ sk_E)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '10'])).
% 0.20/0.50  thf('12', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (((m1_subset_1 @ (sk_D @ sk_G @ sk_E @ sk_B) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.50  thf('16', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((m1_subset_1 @ (sk_D @ sk_G @ sk_E @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.50         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)
% 0.20/0.50        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.50         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)))),
% 0.20/0.50      inference('split', [status(esa)], ['18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.50           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)
% 0.20/0.50        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.50           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)
% 0.20/0.50        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)) | 
% 0.20/0.50       ~
% 0.20/0.50       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.50         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G))),
% 0.20/0.50      inference('split', [status(esa)], ['22'])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('25', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.50          | ~ (v3_pre_topc @ X4 @ X5)
% 0.20/0.50          | (r1_tarski @ (sk_D @ X6 @ X4 @ X5) @ X4)
% 0.20/0.50          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (l1_pre_topc @ X5)
% 0.20/0.50          | ~ (v2_pre_topc @ X5)
% 0.20/0.50          | (v2_struct_0 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_E)
% 0.20/0.50          | (r1_tarski @ (sk_D @ X0 @ sk_E @ sk_B) @ sk_E)
% 0.20/0.50          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_E)
% 0.20/0.50          | (r1_tarski @ (sk_D @ X0 @ sk_E @ sk_B) @ sk_E))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_E)
% 0.20/0.50        | ~ (r2_hidden @ sk_G @ sk_E)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '32'])).
% 0.20/0.50  thf('34', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_E) | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain, ((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_E)),
% 0.20/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ sk_E)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (sk_D @ sk_G @ sk_E @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ X0)
% 0.20/0.50          | (r2_hidden @ (sk_C @ X0 @ (sk_D @ sk_G @ sk_E @ sk_B)) @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '39'])).
% 0.20/0.50  thf('41', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ X0)
% 0.20/0.50          | (r2_hidden @ (sk_C @ X0 @ (sk_D @ sk_G @ sk_E @ sk_B)) @ 
% 0.20/0.50             (u1_struct_0 @ sk_D_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.20/0.50        | (r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.50         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)
% 0.20/0.50        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.50         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)
% 0.20/0.50        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G))),
% 0.20/0.50      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)))),
% 0.20/0.50      inference('split', [status(esa)], ['50'])).
% 0.20/0.50  thf('52', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.50          | ~ (v3_pre_topc @ X4 @ X5)
% 0.20/0.50          | (m1_connsp_2 @ (sk_D @ X6 @ X4 @ X5) @ X5 @ X6)
% 0.20/0.50          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (l1_pre_topc @ X5)
% 0.20/0.50          | ~ (v2_pre_topc @ X5)
% 0.20/0.50          | (v2_struct_0 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_E)
% 0.20/0.50          | (m1_connsp_2 @ (sk_D @ X0 @ sk_E @ sk_B) @ sk_B @ X0)
% 0.20/0.50          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('58', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_E)
% 0.20/0.50          | (m1_connsp_2 @ (sk_D @ X0 @ sk_E @ sk_B) @ sk_B @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (((m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ sk_G)
% 0.20/0.50        | ~ (r2_hidden @ sk_G @ sk_E)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '59'])).
% 0.20/0.50  thf('61', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ sk_G)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('64', plain, ((m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ sk_G)),
% 0.20/0.50      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      ((m1_subset_1 @ (sk_D @ sk_G @ sk_E @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_2 @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t65_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                 ( m1_subset_1 @
% 0.20/0.50                   C @ 
% 0.20/0.50                   ( k1_zfmisc_1 @
% 0.20/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( m1_subset_1 @
% 0.20/0.50                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.50                       ( ![F:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                           ( ![G:$i]:
% 0.20/0.50                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.50                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.20/0.50                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.50                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.50                                   ( r1_tmap_1 @
% 0.20/0.50                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X8)
% 0.20/0.50          | ~ (v2_pre_topc @ X8)
% 0.20/0.50          | ~ (l1_pre_topc @ X8)
% 0.20/0.50          | (v2_struct_0 @ X9)
% 0.20/0.50          | ~ (m1_pre_topc @ X9 @ X8)
% 0.20/0.50          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.50          | ~ (r1_tarski @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.50          | ~ (m1_connsp_2 @ X11 @ X8 @ X10)
% 0.20/0.50          | ((X10) != (X12))
% 0.20/0.50          | ~ (r1_tmap_1 @ X8 @ X13 @ X14 @ X10)
% 0.20/0.50          | (r1_tmap_1 @ X9 @ X13 @ (k2_tmap_1 @ X8 @ X13 @ X14 @ X9) @ X12)
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.50          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))))
% 0.20/0.50          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))
% 0.20/0.50          | ~ (v1_funct_1 @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X13)
% 0.20/0.50          | ~ (v2_pre_topc @ X13)
% 0.20/0.50          | (v2_struct_0 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X13)
% 0.20/0.50          | ~ (v2_pre_topc @ X13)
% 0.20/0.50          | ~ (l1_pre_topc @ X13)
% 0.20/0.50          | ~ (v1_funct_1 @ X14)
% 0.20/0.50          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))
% 0.20/0.50          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))))
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.50          | (r1_tmap_1 @ X9 @ X13 @ (k2_tmap_1 @ X8 @ X13 @ X14 @ X9) @ X12)
% 0.20/0.50          | ~ (r1_tmap_1 @ X8 @ X13 @ X14 @ X12)
% 0.20/0.50          | ~ (m1_connsp_2 @ X11 @ X8 @ X12)
% 0.20/0.50          | ~ (r1_tarski @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X8))
% 0.20/0.50          | ~ (m1_pre_topc @ X9 @ X8)
% 0.20/0.50          | (v2_struct_0 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X8)
% 0.20/0.50          | ~ (v2_pre_topc @ X8)
% 0.20/0.50          | (v2_struct_0 @ X8))),
% 0.20/0.50      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ 
% 0.20/0.50             X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.50          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.50               (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['66', '68'])).
% 0.20/0.50  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('73', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ 
% 0.20/0.50             X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['69', '70', '71', '72', '73', '74', '75'])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ 
% 0.20/0.50             X1)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.20/0.50          | ~ (m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ X1)
% 0.20/0.50          | ~ (r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['65', '76'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ 
% 0.20/0.50             sk_G)
% 0.20/0.50          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '77'])).
% 0.20/0.50  thf('79', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ 
% 0.20/0.50             sk_G)
% 0.20/0.50          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((v2_struct_0 @ sk_A)
% 0.20/0.50           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.20/0.50           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.50              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ sk_G)
% 0.20/0.50           | ~ (r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50           | (v2_struct_0 @ X0)
% 0.20/0.50           | (v2_struct_0 @ sk_B)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '80'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_B)
% 0.20/0.50         | (v2_struct_0 @ sk_D_1)
% 0.20/0.50         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.20/0.50         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.50            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)
% 0.20/0.51         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '81'])).
% 0.20/0.51  thf('83', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('84', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B)
% 0.20/0.51         | (v2_struct_0 @ sk_D_1)
% 0.20/0.51         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)))),
% 0.20/0.51      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)
% 0.20/0.51        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)))),
% 0.20/0.51      inference('split', [status(esa)], ['86'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['85', '87'])).
% 0.20/0.51  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('90', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)))),
% 0.20/0.51      inference('clc', [status(thm)], ['88', '89'])).
% 0.20/0.51  thf('91', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_D_1))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)))),
% 0.20/0.51      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.51  thf('93', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)) | 
% 0.20/0.51       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G))),
% 0.20/0.51      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)) | 
% 0.20/0.51       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G))),
% 0.20/0.51      inference('split', [status(esa)], ['50'])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['23', '94', '95'])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.51        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_G)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['19', '96'])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_2 @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('99', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X8)
% 0.20/0.51          | ~ (v2_pre_topc @ X8)
% 0.20/0.51          | ~ (l1_pre_topc @ X8)
% 0.20/0.51          | (v2_struct_0 @ X9)
% 0.20/0.51          | ~ (m1_pre_topc @ X9 @ X8)
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.51          | ~ (r1_tarski @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (m1_connsp_2 @ X11 @ X8 @ X10)
% 0.20/0.51          | ((X10) != (X12))
% 0.20/0.51          | ~ (r1_tmap_1 @ X9 @ X13 @ (k2_tmap_1 @ X8 @ X13 @ X14 @ X9) @ X12)
% 0.20/0.51          | (r1_tmap_1 @ X8 @ X13 @ X14 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))))
% 0.20/0.51          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))
% 0.20/0.51          | ~ (v1_funct_1 @ X14)
% 0.20/0.51          | ~ (l1_pre_topc @ X13)
% 0.20/0.51          | ~ (v2_pre_topc @ X13)
% 0.20/0.51          | (v2_struct_0 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.51  thf('100', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X13)
% 0.20/0.51          | ~ (v2_pre_topc @ X13)
% 0.20/0.51          | ~ (l1_pre_topc @ X13)
% 0.20/0.51          | ~ (v1_funct_1 @ X14)
% 0.20/0.51          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X13))))
% 0.20/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.51          | (r1_tmap_1 @ X8 @ X13 @ X14 @ X12)
% 0.20/0.51          | ~ (r1_tmap_1 @ X9 @ X13 @ (k2_tmap_1 @ X8 @ X13 @ X14 @ X9) @ X12)
% 0.20/0.51          | ~ (m1_connsp_2 @ X11 @ X8 @ X12)
% 0.20/0.51          | ~ (r1_tarski @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X8))
% 0.20/0.51          | ~ (m1_pre_topc @ X9 @ X8)
% 0.20/0.51          | (v2_struct_0 @ X9)
% 0.20/0.51          | ~ (l1_pre_topc @ X8)
% 0.20/0.51          | ~ (v2_pre_topc @ X8)
% 0.20/0.51          | (v2_struct_0 @ X8))),
% 0.20/0.51      inference('simplify', [status(thm)], ['99'])).
% 0.20/0.51  thf('101', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.51          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ X1)
% 0.20/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['98', '100'])).
% 0.20/0.51  thf('102', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('105', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('108', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.51          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ X1)
% 0.20/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['101', '102', '103', '104', '105', '106', '107'])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)
% 0.20/0.51          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_D_1)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['97', '108'])).
% 0.20/0.51  thf('110', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('111', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('112', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('113', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)
% 0.20/0.51          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | (v2_struct_0 @ sk_D_1)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.20/0.51  thf('114', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | ~ (r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51        | ~ (m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ sk_G)
% 0.20/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '113'])).
% 0.20/0.51  thf('115', plain,
% 0.20/0.51      ((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.51  thf('116', plain,
% 0.20/0.51      ((m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ sk_G)),
% 0.20/0.51      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.51  thf('117', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.20/0.51  thf('118', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F))
% 0.20/0.51         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F)))),
% 0.20/0.51      inference('split', [status(esa)], ['86'])).
% 0.20/0.51  thf('119', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('120', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G))
% 0.20/0.51         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['118', '119'])).
% 0.20/0.51  thf('121', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F)))),
% 0.20/0.51      inference('split', [status(esa)], ['18'])).
% 0.20/0.51  thf('122', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('123', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['121', '122'])).
% 0.20/0.51  thf('124', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G))
% 0.20/0.51         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)))),
% 0.20/0.51      inference('split', [status(esa)], ['22'])).
% 0.20/0.51  thf('125', plain,
% 0.20/0.51      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F)) | 
% 0.20/0.51       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G))),
% 0.20/0.51      inference('sup-', [status(thm)], ['123', '124'])).
% 0.20/0.51  thf('126', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_F))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['23', '94', '125'])).
% 0.20/0.51  thf('127', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_G)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['120', '126'])).
% 0.20/0.51  thf('128', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['117', '127'])).
% 0.20/0.51  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('130', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('clc', [status(thm)], ['128', '129'])).
% 0.20/0.51  thf('131', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('132', plain, ((v2_struct_0 @ sk_D_1)),
% 0.20/0.51      inference('clc', [status(thm)], ['130', '131'])).
% 0.20/0.51  thf('133', plain, ($false), inference('demod', [status(thm)], ['0', '132'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
