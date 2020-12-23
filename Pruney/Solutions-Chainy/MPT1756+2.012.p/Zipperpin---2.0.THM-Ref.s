%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7KXfuB9UN7

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 388 expanded)
%              Number of leaves         :   29 ( 120 expanded)
%              Depth                    :   22
%              Number of atoms          : 1758 (15386 expanded)
%              Number of equality atoms :   12 ( 201 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( r1_tmap_1 @ X11 @ X13 @ ( k2_tmap_1 @ X10 @ X13 @ X14 @ X11 ) @ X12 )
      | ( X15 != X12 )
      | ~ ( r1_tmap_1 @ X10 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_tmap_1 @ X10 @ X13 @ X14 @ X12 )
      | ( r1_tmap_1 @ X11 @ X13 @ ( k2_tmap_1 @ X10 @ X13 @ X14 @ X11 ) @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['28','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['24','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['27'])).

thf('56',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['23','54','55'])).

thf('57',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['19','56'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_tarski @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_connsp_2 @ X19 @ X16 @ X18 )
      | ( X18 != X20 )
      | ~ ( r1_tmap_1 @ X17 @ X21 @ ( k2_tmap_1 @ X16 @ X21 @ X22 @ X17 ) @ X20 )
      | ( r1_tmap_1 @ X16 @ X21 @ X22 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( r1_tmap_1 @ X16 @ X21 @ X22 @ X20 )
      | ~ ( r1_tmap_1 @ X17 @ X21 @ ( k2_tmap_1 @ X16 @ X21 @ X22 @ X17 ) @ X20 )
      | ~ ( m1_connsp_2 @ X19 @ X16 @ X20 )
      | ~ ( r1_tarski @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
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
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
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
    inference(demod,[status(thm)],['61','62','63','64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('72',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','73'])).

thf('75',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ( r1_tarski @ ( sk_D @ X8 @ X6 @ X7 ) @ X6 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_E @ sk_B ) @ sk_E )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_E @ sk_B ) @ sk_E ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_E )
    | ~ ( r2_hidden @ sk_G @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['12','13'])).

thf('86',plain,
    ( ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_E ),
    inference(clc,[status(thm)],['86','87'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['75','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('93',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ( m1_connsp_2 @ ( sk_D @ X8 @ X6 @ X7 ) @ X7 @ X8 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_E @ sk_B ) @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_E @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ sk_G )
    | ~ ( r2_hidden @ sk_G @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['12','13'])).

thf('102',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_connsp_2 @ ( sk_D @ sk_G @ sk_E @ sk_B ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','91','104'])).

thf('106',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['46'])).

thf('107',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('110',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['22'])).

thf('113',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['23','54','113'])).

thf('115',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['108','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['0','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7KXfuB9UN7
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 77 iterations in 0.051s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.22/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(t66_tmap_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52                 ( m1_subset_1 @
% 0.22/0.52                   C @ 
% 0.22/0.52                   ( k1_zfmisc_1 @
% 0.22/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.52                   ( ![E:$i]:
% 0.22/0.52                     ( ( m1_subset_1 @
% 0.22/0.52                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.52                       ( ![F:$i]:
% 0.22/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.52                           ( ![G:$i]:
% 0.22/0.52                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.22/0.52                                   ( r2_hidden @ F @ E ) & 
% 0.22/0.52                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.22/0.52                                   ( ( F ) = ( G ) ) ) =>
% 0.22/0.52                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.22/0.52                                   ( r1_tmap_1 @
% 0.22/0.52                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52            ( l1_pre_topc @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52                ( l1_pre_topc @ B ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52                    ( v1_funct_2 @
% 0.22/0.52                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52                    ( m1_subset_1 @
% 0.22/0.52                      C @ 
% 0.22/0.52                      ( k1_zfmisc_1 @
% 0.22/0.52                        ( k2_zfmisc_1 @
% 0.22/0.52                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.52                  ( ![D:$i]:
% 0.22/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.52                      ( ![E:$i]:
% 0.22/0.52                        ( ( m1_subset_1 @
% 0.22/0.52                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.52                          ( ![F:$i]:
% 0.22/0.52                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.52                              ( ![G:$i]:
% 0.22/0.52                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.22/0.52                                      ( r2_hidden @ F @ E ) & 
% 0.22/0.52                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.22/0.52                                      ( ( F ) = ( G ) ) ) =>
% 0.22/0.52                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.22/0.52                                      ( r1_tmap_1 @
% 0.22/0.52                                        D @ A @ 
% 0.22/0.52                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.22/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('2', plain, (((sk_F) = (sk_G))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('3', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t9_connsp_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.52             ( ![C:$i]:
% 0.22/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.22/0.52                      ( ![D:$i]:
% 0.22/0.52                        ( ( m1_subset_1 @
% 0.22/0.52                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.22/0.52                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.52          | ~ (v3_pre_topc @ X6 @ X7)
% 0.22/0.52          | (m1_subset_1 @ (sk_D @ X8 @ X6 @ X7) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.52          | ~ (r2_hidden @ X8 @ X6)
% 0.22/0.52          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.22/0.52          | ~ (l1_pre_topc @ X7)
% 0.22/0.52          | ~ (v2_pre_topc @ X7)
% 0.22/0.52          | (v2_struct_0 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_B)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_E)
% 0.22/0.52          | (m1_subset_1 @ (sk_D @ X0 @ sk_E @ sk_B) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.52          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('9', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_B)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_E)
% 0.22/0.52          | (m1_subset_1 @ (sk_D @ X0 @ sk_E @ sk_B) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.52      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (((m1_subset_1 @ (sk_D @ sk_G @ sk_E @ sk_B) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.52        | ~ (r2_hidden @ sk_G @ sk_E)
% 0.22/0.52        | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '10'])).
% 0.22/0.52  thf('12', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain, (((sk_F) = (sk_G))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('14', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (((m1_subset_1 @ (sk_D @ sk_G @ sk_E @ sk_B) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.52        | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '14'])).
% 0.22/0.52  thf('16', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((m1_subset_1 @ (sk_D @ sk_G @ sk_E @ sk_B) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.52      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.52         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.22/0.52        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.52         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.52               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.22/0.52      inference('split', [status(esa)], ['18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.52           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.22/0.52        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('21', plain, (((sk_F) = (sk_G))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.52           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.22/0.52        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.22/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)) | 
% 0.22/0.52       ~
% 0.22/0.52       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.52         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))),
% 0.22/0.52      inference('split', [status(esa)], ['22'])).
% 0.22/0.52  thf('24', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.52         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.22/0.52        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('26', plain, (((sk_F) = (sk_G))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.52         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.22/0.52        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.22/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.22/0.53      inference('split', [status(esa)], ['27'])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t64_tmap_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.53                 ( m1_subset_1 @
% 0.22/0.53                   C @ 
% 0.22/0.53                   ( k1_zfmisc_1 @
% 0.22/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.53                   ( ![E:$i]:
% 0.22/0.53                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.53                       ( ![F:$i]:
% 0.22/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.53                           ( ( ( ( E ) = ( F ) ) & 
% 0.22/0.53                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.22/0.53                             ( r1_tmap_1 @
% 0.22/0.53                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X10)
% 0.22/0.53          | ~ (v2_pre_topc @ X10)
% 0.22/0.53          | ~ (l1_pre_topc @ X10)
% 0.22/0.53          | (v2_struct_0 @ X11)
% 0.22/0.53          | ~ (m1_pre_topc @ X11 @ X10)
% 0.22/0.53          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.22/0.53          | (r1_tmap_1 @ X11 @ X13 @ (k2_tmap_1 @ X10 @ X13 @ X14 @ X11) @ X12)
% 0.22/0.53          | ((X15) != (X12))
% 0.22/0.53          | ~ (r1_tmap_1 @ X10 @ X13 @ X14 @ X15)
% 0.22/0.53          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X10))
% 0.22/0.53          | ~ (m1_subset_1 @ X14 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X13))))
% 0.22/0.53          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X13))
% 0.22/0.53          | ~ (v1_funct_1 @ X14)
% 0.22/0.53          | ~ (l1_pre_topc @ X13)
% 0.22/0.53          | ~ (v2_pre_topc @ X13)
% 0.22/0.53          | (v2_struct_0 @ X13))),
% 0.22/0.53      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X13)
% 0.22/0.53          | ~ (v2_pre_topc @ X13)
% 0.22/0.53          | ~ (l1_pre_topc @ X13)
% 0.22/0.53          | ~ (v1_funct_1 @ X14)
% 0.22/0.53          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X13))
% 0.22/0.53          | ~ (m1_subset_1 @ X14 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X13))))
% 0.22/0.53          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.22/0.53          | ~ (r1_tmap_1 @ X10 @ X13 @ X14 @ X12)
% 0.22/0.53          | (r1_tmap_1 @ X11 @ X13 @ (k2_tmap_1 @ X10 @ X13 @ X14 @ X11) @ X12)
% 0.22/0.53          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.22/0.53          | ~ (m1_pre_topc @ X11 @ X10)
% 0.22/0.53          | (v2_struct_0 @ X11)
% 0.22/0.53          | ~ (l1_pre_topc @ X10)
% 0.22/0.53          | ~ (v2_pre_topc @ X10)
% 0.22/0.53          | (v2_struct_0 @ X10))),
% 0.22/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.22/0.53             X1)
% 0.22/0.53          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53               (u1_struct_0 @ sk_A))
% 0.22/0.53          | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53          | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['29', '31'])).
% 0.22/0.53  thf('33', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('36', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.22/0.53             X1)
% 0.22/0.53          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)],
% 0.22/0.53                ['32', '33', '34', '35', '36', '37', '38'])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          ((v2_struct_0 @ sk_A)
% 0.22/0.53           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.22/0.53           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.22/0.53              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_G)
% 0.22/0.53           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.22/0.53           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.53           | (v2_struct_0 @ X0)
% 0.22/0.53           | (v2_struct_0 @ sk_B)))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['28', '39'])).
% 0.22/0.53  thf('41', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          ((v2_struct_0 @ sk_A)
% 0.22/0.53           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.22/0.53              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_G)
% 0.22/0.53           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.22/0.53           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.53           | (v2_struct_0 @ X0)
% 0.22/0.53           | (v2_struct_0 @ sk_B)))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.53  thf('43', plain,
% 0.22/0.53      ((((v2_struct_0 @ sk_B)
% 0.22/0.53         | (v2_struct_0 @ sk_D_1)
% 0.22/0.53         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.22/0.53         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.22/0.53         | (v2_struct_0 @ sk_A)))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['24', '42'])).
% 0.22/0.53  thf('44', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      ((((v2_struct_0 @ sk_B)
% 0.22/0.53         | (v2_struct_0 @ sk_D_1)
% 0.22/0.53         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.22/0.53         | (v2_struct_0 @ sk_A)))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.22/0.53        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('47', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.22/0.53      inference('split', [status(esa)], ['46'])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) & 
% 0.22/0.53             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['45', '47'])).
% 0.22/0.53  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) & 
% 0.22/0.53             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.22/0.53      inference('clc', [status(thm)], ['48', '49'])).
% 0.22/0.53  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('52', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_D_1))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) & 
% 0.22/0.53             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.22/0.53      inference('clc', [status(thm)], ['50', '51'])).
% 0.22/0.53  thf('53', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) | 
% 0.22/0.53       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.22/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) | 
% 0.22/0.53       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.22/0.53      inference('split', [status(esa)], ['27'])).
% 0.22/0.53  thf('56', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['23', '54', '55'])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.22/0.53        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['19', '56'])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t65_tmap_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.53                 ( m1_subset_1 @
% 0.22/0.53                   C @ 
% 0.22/0.53                   ( k1_zfmisc_1 @
% 0.22/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.53                   ( ![E:$i]:
% 0.22/0.53                     ( ( m1_subset_1 @
% 0.22/0.53                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.53                       ( ![F:$i]:
% 0.22/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.53                           ( ![G:$i]:
% 0.22/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.53                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.22/0.53                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.22/0.53                                   ( ( F ) = ( G ) ) ) =>
% 0.22/0.53                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.22/0.53                                   ( r1_tmap_1 @
% 0.22/0.53                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('59', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X16)
% 0.22/0.53          | ~ (v2_pre_topc @ X16)
% 0.22/0.53          | ~ (l1_pre_topc @ X16)
% 0.22/0.53          | (v2_struct_0 @ X17)
% 0.22/0.53          | ~ (m1_pre_topc @ X17 @ X16)
% 0.22/0.53          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (r1_tarski @ X19 @ (u1_struct_0 @ X17))
% 0.22/0.53          | ~ (m1_connsp_2 @ X19 @ X16 @ X18)
% 0.22/0.53          | ((X18) != (X20))
% 0.22/0.53          | ~ (r1_tmap_1 @ X17 @ X21 @ (k2_tmap_1 @ X16 @ X21 @ X22 @ X17) @ 
% 0.22/0.53               X20)
% 0.22/0.53          | (r1_tmap_1 @ X16 @ X21 @ X22 @ X18)
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))))
% 0.22/0.53          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))
% 0.22/0.53          | ~ (v1_funct_1 @ X22)
% 0.22/0.53          | ~ (l1_pre_topc @ X21)
% 0.22/0.53          | ~ (v2_pre_topc @ X21)
% 0.22/0.53          | (v2_struct_0 @ X21))),
% 0.22/0.53      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.22/0.53  thf('60', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X21)
% 0.22/0.53          | ~ (v2_pre_topc @ X21)
% 0.22/0.53          | ~ (l1_pre_topc @ X21)
% 0.22/0.53          | ~ (v1_funct_1 @ X22)
% 0.22/0.53          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))
% 0.22/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.22/0.53          | (r1_tmap_1 @ X16 @ X21 @ X22 @ X20)
% 0.22/0.53          | ~ (r1_tmap_1 @ X17 @ X21 @ (k2_tmap_1 @ X16 @ X21 @ X22 @ X17) @ 
% 0.22/0.53               X20)
% 0.22/0.53          | ~ (m1_connsp_2 @ X19 @ X16 @ X20)
% 0.22/0.53          | ~ (r1_tarski @ X19 @ (u1_struct_0 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (m1_pre_topc @ X17 @ X16)
% 0.22/0.53          | (v2_struct_0 @ X17)
% 0.22/0.53          | ~ (l1_pre_topc @ X16)
% 0.22/0.53          | ~ (v2_pre_topc @ X16)
% 0.22/0.53          | (v2_struct_0 @ X16))),
% 0.22/0.53      inference('simplify', [status(thm)], ['59'])).
% 0.22/0.53  thf('61', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.22/0.53          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.22/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.22/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.53          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53               (u1_struct_0 @ sk_A))
% 0.22/0.53          | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53          | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['58', '60'])).
% 0.22/0.53  thf('62', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('64', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('65', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('68', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.22/0.53          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.22/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.22/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.53          | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)],
% 0.22/0.53                ['61', '62', '63', '64', '65', '66', '67'])).
% 0.22/0.53  thf('69', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_A)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.53          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))
% 0.22/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.22/0.53          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.22/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.22/0.53          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ sk_D_1)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['57', '68'])).
% 0.22/0.53  thf('70', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('71', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('72', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('73', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_A)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.22/0.53          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.22/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.22/0.53          | (v2_struct_0 @ sk_D_1)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.22/0.53  thf('74', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_B)
% 0.22/0.53        | (v2_struct_0 @ sk_D_1)
% 0.22/0.53        | ~ (r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.22/0.53        | ~ (m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ sk_G)
% 0.22/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.22/0.53        | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '73'])).
% 0.22/0.53  thf('75', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('76', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('77', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('78', plain,
% 0.22/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.53          | ~ (v3_pre_topc @ X6 @ X7)
% 0.22/0.53          | (r1_tarski @ (sk_D @ X8 @ X6 @ X7) @ X6)
% 0.22/0.53          | ~ (r2_hidden @ X8 @ X6)
% 0.22/0.53          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.22/0.53          | ~ (l1_pre_topc @ X7)
% 0.22/0.53          | ~ (v2_pre_topc @ X7)
% 0.22/0.53          | (v2_struct_0 @ X7))),
% 0.22/0.53      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.22/0.53  thf('79', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_E)
% 0.22/0.53          | (r1_tarski @ (sk_D @ X0 @ sk_E @ sk_B) @ sk_E)
% 0.22/0.53          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['77', '78'])).
% 0.22/0.53  thf('80', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('82', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('83', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_E)
% 0.22/0.53          | (r1_tarski @ (sk_D @ X0 @ sk_E @ sk_B) @ sk_E))),
% 0.22/0.53      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.22/0.53  thf('84', plain,
% 0.22/0.53      (((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_E)
% 0.22/0.53        | ~ (r2_hidden @ sk_G @ sk_E)
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['76', '83'])).
% 0.22/0.53  thf('85', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('86', plain,
% 0.22/0.53      (((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_E) | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['84', '85'])).
% 0.22/0.53  thf('87', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('88', plain, ((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_E)),
% 0.22/0.53      inference('clc', [status(thm)], ['86', '87'])).
% 0.22/0.53  thf(t1_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.53       ( r1_tarski @ A @ C ) ))).
% 0.22/0.53  thf('89', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.22/0.53          | (r1_tarski @ X0 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.53  thf('90', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ X0)
% 0.22/0.53          | ~ (r1_tarski @ sk_E @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['88', '89'])).
% 0.22/0.53  thf('91', plain,
% 0.22/0.53      ((r1_tarski @ (sk_D @ sk_G @ sk_E @ sk_B) @ (u1_struct_0 @ sk_D_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['75', '90'])).
% 0.22/0.53  thf('92', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('93', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('94', plain,
% 0.22/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.53          | ~ (v3_pre_topc @ X6 @ X7)
% 0.22/0.53          | (m1_connsp_2 @ (sk_D @ X8 @ X6 @ X7) @ X7 @ X8)
% 0.22/0.53          | ~ (r2_hidden @ X8 @ X6)
% 0.22/0.53          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.22/0.53          | ~ (l1_pre_topc @ X7)
% 0.22/0.53          | ~ (v2_pre_topc @ X7)
% 0.22/0.53          | (v2_struct_0 @ X7))),
% 0.22/0.53      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.22/0.53  thf('95', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_E)
% 0.22/0.53          | (m1_connsp_2 @ (sk_D @ X0 @ sk_E @ sk_B) @ sk_B @ X0)
% 0.22/0.53          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.53  thf('96', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('98', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('99', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_E)
% 0.22/0.53          | (m1_connsp_2 @ (sk_D @ X0 @ sk_E @ sk_B) @ sk_B @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 0.22/0.53  thf('100', plain,
% 0.22/0.53      (((m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ sk_G)
% 0.22/0.53        | ~ (r2_hidden @ sk_G @ sk_E)
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['92', '99'])).
% 0.22/0.53  thf('101', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('102', plain,
% 0.22/0.53      (((m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ sk_G)
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['100', '101'])).
% 0.22/0.53  thf('103', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('104', plain,
% 0.22/0.53      ((m1_connsp_2 @ (sk_D @ sk_G @ sk_E @ sk_B) @ sk_B @ sk_G)),
% 0.22/0.53      inference('clc', [status(thm)], ['102', '103'])).
% 0.22/0.53  thf('105', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_B)
% 0.22/0.53        | (v2_struct_0 @ sk_D_1)
% 0.22/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.22/0.53        | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['74', '91', '104'])).
% 0.22/0.53  thf('106', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.22/0.53         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.22/0.53      inference('split', [status(esa)], ['46'])).
% 0.22/0.53  thf('107', plain, (((sk_F) = (sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('108', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.22/0.53         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.22/0.53      inference('demod', [status(thm)], ['106', '107'])).
% 0.22/0.53  thf('109', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.22/0.53      inference('split', [status(esa)], ['18'])).
% 0.22/0.53  thf('110', plain, (((sk_F) = (sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('111', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.22/0.53      inference('demod', [status(thm)], ['109', '110'])).
% 0.22/0.53  thf('112', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.22/0.53         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.22/0.53      inference('split', [status(esa)], ['22'])).
% 0.22/0.53  thf('113', plain,
% 0.22/0.53      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)) | 
% 0.22/0.53       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.22/0.53      inference('sup-', [status(thm)], ['111', '112'])).
% 0.22/0.53  thf('114', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['23', '54', '113'])).
% 0.22/0.53  thf('115', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['108', '114'])).
% 0.22/0.53  thf('116', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['105', '115'])).
% 0.22/0.53  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('118', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.22/0.53      inference('clc', [status(thm)], ['116', '117'])).
% 0.22/0.53  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('120', plain, ((v2_struct_0 @ sk_D_1)),
% 0.22/0.53      inference('clc', [status(thm)], ['118', '119'])).
% 0.22/0.53  thf('121', plain, ($false), inference('demod', [status(thm)], ['0', '120'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
