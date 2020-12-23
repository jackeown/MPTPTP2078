%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4kQfKp1OpL

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 314 expanded)
%              Number of leaves         :   28 ( 102 expanded)
%              Depth                    :   20
%              Number of atoms          : 1731 (12194 expanded)
%              Number of equality atoms :   20 ( 180 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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

thf('0',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_tarski @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_connsp_2 @ X10 @ X7 @ X9 )
      | ( X9 != X11 )
      | ~ ( r1_tmap_1 @ X7 @ X12 @ X13 @ X9 )
      | ( r1_tmap_1 @ X8 @ X12 @ ( k2_tmap_1 @ X7 @ X12 @ X13 @ X8 ) @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('10',plain,(
    ! [X7: $i,X8: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ( r1_tmap_1 @ X8 @ X12 @ ( k2_tmap_1 @ X7 @ X12 @ X13 @ X8 ) @ X11 )
      | ~ ( r1_tmap_1 @ X7 @ X12 @ X13 @ X11 )
      | ~ ( m1_connsp_2 @ X10 @ X7 @ X11 )
      | ~ ( r1_tarski @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X1 )
      | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('25',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ ( k1_tops_1 @ X5 @ X6 ) )
      | ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('32',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v3_pre_topc @ X1 @ X0 )
        | ( ( k1_tops_1 @ X0 @ X1 )
          = X1 ) )
   <= ! [X0: $i,X1: $i] :
        ( ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v3_pre_topc @ X1 @ X0 )
        | ( ( k1_tops_1 @ X0 @ X1 )
          = X1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('35',plain,
    ( ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) )
   <= ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v3_pre_topc @ X1 @ X0 )
        | ( ( k1_tops_1 @ X0 @ X1 )
          = X1 ) )
    | ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = X1 ) ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = X1 ) ) ),
    inference(simpl_trail,[status(thm)],['32','41'])).

thf('43',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_E )
      = sk_E )
    | ~ ( v3_pre_topc @ sk_E @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_B @ sk_E )
    = sk_E ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_G @ sk_E )
    | ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','47'])).

thf('49',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['20','23','54'])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['2','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['3'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['3'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_tarski @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_connsp_2 @ X10 @ X7 @ X9 )
      | ( X9 != X11 )
      | ~ ( r1_tmap_1 @ X8 @ X12 @ ( k2_tmap_1 @ X7 @ X12 @ X13 @ X8 ) @ X11 )
      | ( r1_tmap_1 @ X7 @ X12 @ X13 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('73',plain,(
    ! [X7: $i,X8: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ( r1_tmap_1 @ X7 @ X12 @ X13 @ X11 )
      | ~ ( r1_tmap_1 @ X8 @ X12 @ ( k2_tmap_1 @ X7 @ X12 @ X13 @ X8 ) @ X11 )
      | ~ ( m1_connsp_2 @ X10 @ X7 @ X11 )
      | ~ ( r1_tarski @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
        | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_pre_topc @ sk_D @ sk_B )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('85',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
        | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference('sup-',[status(thm)],['69','86'])).

thf('88',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['52','53'])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
      & ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
      & ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
      & ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','67','68','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4kQfKp1OpL
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 55 iterations in 0.031s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.48  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.48  thf(t66_tmap_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.48             ( l1_pre_topc @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48                 ( m1_subset_1 @
% 0.20/0.48                   C @ 
% 0.20/0.48                   ( k1_zfmisc_1 @
% 0.20/0.48                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.48                   ( ![E:$i]:
% 0.20/0.48                     ( ( m1_subset_1 @
% 0.20/0.48                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.48                       ( ![F:$i]:
% 0.20/0.48                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                           ( ![G:$i]:
% 0.20/0.48                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.48                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.20/0.48                                   ( r2_hidden @ F @ E ) & 
% 0.20/0.48                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.48                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.48                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.48                                   ( r1_tmap_1 @
% 0.20/0.48                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48            ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.48                ( l1_pre_topc @ B ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48                    ( v1_funct_2 @
% 0.20/0.48                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48                    ( m1_subset_1 @
% 0.20/0.48                      C @ 
% 0.20/0.48                      ( k1_zfmisc_1 @
% 0.20/0.48                        ( k2_zfmisc_1 @
% 0.20/0.48                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.48                  ( ![D:$i]:
% 0.20/0.48                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.48                      ( ![E:$i]:
% 0.20/0.48                        ( ( m1_subset_1 @
% 0.20/0.48                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.48                          ( ![F:$i]:
% 0.20/0.48                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                              ( ![G:$i]:
% 0.20/0.48                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.48                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.20/0.48                                      ( r2_hidden @ F @ E ) & 
% 0.20/0.48                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.48                                      ( ( F ) = ( G ) ) ) =>
% 0.20/0.48                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.48                                      ( r1_tmap_1 @
% 0.20/0.48                                        D @ A @ 
% 0.20/0.48                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.48           sk_G)
% 0.20/0.48        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.48         sk_G)) | 
% 0.20/0.48       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.48         sk_G)
% 0.20/0.48        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('5', plain, (((sk_F) = (sk_G))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t65_tmap_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.48             ( l1_pre_topc @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48                 ( m1_subset_1 @
% 0.20/0.48                   C @ 
% 0.20/0.48                   ( k1_zfmisc_1 @
% 0.20/0.48                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.48                   ( ![E:$i]:
% 0.20/0.48                     ( ( m1_subset_1 @
% 0.20/0.48                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.48                       ( ![F:$i]:
% 0.20/0.48                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                           ( ![G:$i]:
% 0.20/0.48                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.48                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.48                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.20/0.48                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.48                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.48                                   ( r1_tmap_1 @
% 0.20/0.48                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | (v2_struct_0 @ X8)
% 0.20/0.48          | ~ (m1_pre_topc @ X8 @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ~ (r1_tarski @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ~ (m1_connsp_2 @ X10 @ X7 @ X9)
% 0.20/0.48          | ((X9) != (X11))
% 0.20/0.48          | ~ (r1_tmap_1 @ X7 @ X12 @ X13 @ X9)
% 0.20/0.48          | (r1_tmap_1 @ X8 @ X12 @ (k2_tmap_1 @ X7 @ X12 @ X13 @ X8) @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.48               (k1_zfmisc_1 @ 
% 0.20/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X12))))
% 0.20/0.48          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X12))
% 0.20/0.48          | ~ (v1_funct_1 @ X13)
% 0.20/0.48          | ~ (l1_pre_topc @ X12)
% 0.20/0.48          | ~ (v2_pre_topc @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X12)
% 0.20/0.48          | ~ (v2_pre_topc @ X12)
% 0.20/0.48          | ~ (l1_pre_topc @ X12)
% 0.20/0.48          | ~ (v1_funct_1 @ X13)
% 0.20/0.48          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X12))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.48               (k1_zfmisc_1 @ 
% 0.20/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X12))))
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.48          | (r1_tmap_1 @ X8 @ X12 @ (k2_tmap_1 @ X7 @ X12 @ X13 @ X8) @ X11)
% 0.20/0.48          | ~ (r1_tmap_1 @ X7 @ X12 @ X13 @ X11)
% 0.20/0.48          | ~ (m1_connsp_2 @ X10 @ X7 @ X11)
% 0.20/0.48          | ~ (r1_tarski @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ~ (m1_pre_topc @ X8 @ X7)
% 0.20/0.48          | (v2_struct_0 @ X8)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | (v2_struct_0 @ X7))),
% 0.20/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.48          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.20/0.48          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.48          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.48  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.48          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.20/0.48          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)],
% 0.20/0.48                ['11', '12', '13', '14', '15', '16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.20/0.48          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.20/0.48          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X1)
% 0.20/0.48          | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((v2_struct_0 @ sk_B)
% 0.20/0.48           | (v2_struct_0 @ X0)
% 0.20/0.48           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.48           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.48           | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.20/0.48           | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.20/0.48           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.20/0.48              sk_G)
% 0.20/0.48           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.20/0.48           | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '19'])).
% 0.20/0.48  thf('21', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, (((sk_F) = (sk_G))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d1_connsp_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.48                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.48          | ~ (r2_hidden @ X4 @ (k1_tops_1 @ X5 @ X6))
% 0.20/0.48          | (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.48          | ~ (l1_pre_topc @ X5)
% 0.20/0.48          | ~ (v2_pre_topc @ X5)
% 0.20/0.48          | (v2_struct_0 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.48          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t55_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( l1_pre_topc @ B ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.48                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.20/0.48                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.20/0.48                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.20/0.48                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (v3_pre_topc @ X1 @ X0)
% 0.20/0.48          | ((k1_tops_1 @ X0 @ X1) = (X1))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48          | ~ (l1_pre_topc @ X3)
% 0.20/0.48          | ~ (v2_pre_topc @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i]:
% 0.20/0.48          (~ (l1_pre_topc @ X0)
% 0.20/0.48           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48           | ~ (v3_pre_topc @ X1 @ X0)
% 0.20/0.48           | ((k1_tops_1 @ X0 @ X1) = (X1))))
% 0.20/0.48         <= ((![X0 : $i, X1 : $i]:
% 0.20/0.48                (~ (l1_pre_topc @ X0)
% 0.20/0.48                 | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48                 | ~ (v3_pre_topc @ X1 @ X0)
% 0.20/0.48                 | ((k1_tops_1 @ X0 @ X1) = (X1)))))),
% 0.20/0.48      inference('split', [status(esa)], ['31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (v3_pre_topc @ X1 @ X0)
% 0.20/0.48          | ((k1_tops_1 @ X0 @ X1) = (X1))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48          | ~ (l1_pre_topc @ X3)
% 0.20/0.48          | ~ (v2_pre_topc @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((![X2 : $i, X3 : $i]:
% 0.20/0.48          (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48           | ~ (l1_pre_topc @ X3)
% 0.20/0.48           | ~ (v2_pre_topc @ X3)))
% 0.20/0.48         <= ((![X2 : $i, X3 : $i]:
% 0.20/0.48                (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48                 | ~ (l1_pre_topc @ X3)
% 0.20/0.48                 | ~ (v2_pre_topc @ X3))))),
% 0.20/0.48      inference('split', [status(esa)], ['34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B)))
% 0.20/0.48         <= ((![X2 : $i, X3 : $i]:
% 0.20/0.48                (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48                 | ~ (l1_pre_topc @ X3)
% 0.20/0.48                 | ~ (v2_pre_topc @ X3))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.48  thf('37', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (~
% 0.20/0.48       (![X2 : $i, X3 : $i]:
% 0.20/0.48          (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48           | ~ (l1_pre_topc @ X3)
% 0.20/0.48           | ~ (v2_pre_topc @ X3)))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i]:
% 0.20/0.48          (~ (l1_pre_topc @ X0)
% 0.20/0.48           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48           | ~ (v3_pre_topc @ X1 @ X0)
% 0.20/0.48           | ((k1_tops_1 @ X0 @ X1) = (X1)))) | 
% 0.20/0.48       (![X2 : $i, X3 : $i]:
% 0.20/0.48          (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.48           | ~ (l1_pre_topc @ X3)
% 0.20/0.48           | ~ (v2_pre_topc @ X3)))),
% 0.20/0.48      inference('split', [status(esa)], ['31'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i]:
% 0.20/0.48          (~ (l1_pre_topc @ X0)
% 0.20/0.48           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48           | ~ (v3_pre_topc @ X1 @ X0)
% 0.20/0.48           | ((k1_tops_1 @ X0 @ X1) = (X1))))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (v3_pre_topc @ X1 @ X0)
% 0.20/0.48          | ((k1_tops_1 @ X0 @ X1) = (X1)))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['32', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((((k1_tops_1 @ sk_B @ sk_E) = (sk_E))
% 0.20/0.48        | ~ (v3_pre_topc @ sk_E @ sk_B)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '42'])).
% 0.20/0.48  thf('44', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('46', plain, (((k1_tops_1 @ sk_B @ sk_E) = (sk_E))),
% 0.20/0.48      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ sk_E)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28', '29', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_G @ sk_E)
% 0.20/0.48        | (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.20/0.48        | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '47'])).
% 0.20/0.48  thf('49', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain, (((sk_F) = (sk_G))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (((m1_connsp_2 @ sk_E @ sk_B @ sk_G) | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['48', '51'])).
% 0.20/0.48  thf('53', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('54', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.20/0.48      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((v2_struct_0 @ sk_B)
% 0.20/0.48           | (v2_struct_0 @ X0)
% 0.20/0.48           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.48           | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.20/0.48           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.20/0.48              sk_G)
% 0.20/0.48           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.20/0.48           | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '23', '54'])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A)
% 0.20/0.48         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.48         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)
% 0.20/0.48         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.48         | (v2_struct_0 @ sk_D)
% 0.20/0.48         | (v2_struct_0 @ sk_B)))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '55'])).
% 0.20/0.48  thf('57', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('58', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A)
% 0.20/0.48         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)
% 0.20/0.48         | (v2_struct_0 @ sk_D)
% 0.20/0.48         | (v2_struct_0 @ sk_B)))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.48           sk_G))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)) & 
% 0.20/0.48             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.48  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)) & 
% 0.20/0.48             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.48  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_D))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)) & 
% 0.20/0.48             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('clc', [status(thm)], ['63', '64'])).
% 0.20/0.48  thf('66', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.48         sk_G)) | 
% 0.20/0.48       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.20/0.48      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.48         sk_G)) | 
% 0.20/0.48       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.48         sk_G))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('71', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('72', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | (v2_struct_0 @ X8)
% 0.20/0.48          | ~ (m1_pre_topc @ X8 @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ~ (r1_tarski @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ~ (m1_connsp_2 @ X10 @ X7 @ X9)
% 0.20/0.48          | ((X9) != (X11))
% 0.20/0.48          | ~ (r1_tmap_1 @ X8 @ X12 @ (k2_tmap_1 @ X7 @ X12 @ X13 @ X8) @ X11)
% 0.20/0.48          | (r1_tmap_1 @ X7 @ X12 @ X13 @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.48               (k1_zfmisc_1 @ 
% 0.20/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X12))))
% 0.20/0.48          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X12))
% 0.20/0.48          | ~ (v1_funct_1 @ X13)
% 0.20/0.48          | ~ (l1_pre_topc @ X12)
% 0.20/0.48          | ~ (v2_pre_topc @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.48  thf('73', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X12)
% 0.20/0.48          | ~ (v2_pre_topc @ X12)
% 0.20/0.48          | ~ (l1_pre_topc @ X12)
% 0.20/0.48          | ~ (v1_funct_1 @ X13)
% 0.20/0.48          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X12))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.48               (k1_zfmisc_1 @ 
% 0.20/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X12))))
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.20/0.48          | (r1_tmap_1 @ X7 @ X12 @ X13 @ X11)
% 0.20/0.48          | ~ (r1_tmap_1 @ X8 @ X12 @ (k2_tmap_1 @ X7 @ X12 @ X13 @ X8) @ X11)
% 0.20/0.48          | ~ (m1_connsp_2 @ X10 @ X7 @ X11)
% 0.20/0.48          | ~ (r1_tarski @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ~ (m1_pre_topc @ X8 @ X7)
% 0.20/0.48          | (v2_struct_0 @ X8)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | (v2_struct_0 @ X7))),
% 0.20/0.48      inference('simplify', [status(thm)], ['72'])).
% 0.20/0.48  thf('74', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.48          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.20/0.48               X1)
% 0.20/0.48          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.48          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['71', '73'])).
% 0.20/0.48  thf('75', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('76', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('77', plain,
% 0.20/0.48      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('81', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.48          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.20/0.48               X1)
% 0.20/0.48          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)],
% 0.20/0.48                ['74', '75', '76', '77', '78', '79', '80'])).
% 0.20/0.48  thf('82', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((v2_struct_0 @ sk_A)
% 0.20/0.48           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.48           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.48           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.20/0.48           | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.20/0.48           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.48           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.20/0.48           | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.48           | (v2_struct_0 @ sk_D)
% 0.20/0.48           | (v2_struct_0 @ sk_B)))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['70', '81'])).
% 0.20/0.48  thf('83', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('84', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('85', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('86', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((v2_struct_0 @ sk_A)
% 0.20/0.48           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.48           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.20/0.48           | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.20/0.48           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.48           | (v2_struct_0 @ sk_D)
% 0.20/0.48           | (v2_struct_0 @ sk_B)))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.48      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.20/0.48  thf('87', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_B)
% 0.20/0.48         | (v2_struct_0 @ sk_D)
% 0.20/0.48         | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))
% 0.20/0.48         | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.20/0.48         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.20/0.48         | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['69', '86'])).
% 0.20/0.48  thf('88', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('89', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.20/0.48      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.48  thf('90', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_B)
% 0.20/0.48         | (v2_struct_0 @ sk_D)
% 0.20/0.48         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.20/0.48         | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.48      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.20/0.48  thf('91', plain,
% 0.20/0.48      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))
% 0.20/0.48         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('92', plain, (((sk_F) = (sk_G))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('93', plain,
% 0.20/0.48      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.20/0.48         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.20/0.48      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.48  thf('94', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.48         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)) & 
% 0.20/0.48             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['90', '93'])).
% 0.20/0.48  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('96', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.48         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)) & 
% 0.20/0.48             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.48      inference('clc', [status(thm)], ['94', '95'])).
% 0.20/0.48  thf('97', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('98', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_D))
% 0.20/0.48         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)) & 
% 0.20/0.48             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.20/0.48               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.48      inference('clc', [status(thm)], ['96', '97'])).
% 0.20/0.48  thf('99', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('100', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.48         sk_G)) | 
% 0.20/0.48       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.20/0.48      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.48  thf('101', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['1', '67', '68', '100'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
