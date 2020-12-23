%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1712+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9VO78n2ZmO

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:07 EST 2020

% Result     : Theorem 24.21s
% Output     : Refutation 24.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 339 expanded)
%              Number of leaves         :   29 ( 108 expanded)
%              Depth                    :   26
%              Number of atoms          : 2058 (10939 expanded)
%              Number of equality atoms :   20 ( 346 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i > $i )).

thf(t21_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ( ( ( E = D )
                              & ( F = D ) )
                           => ! [G: $i] :
                                ( ( m1_connsp_2 @ G @ B @ E )
                               => ! [H: $i] :
                                    ( ( m1_connsp_2 @ H @ C @ F )
                                   => ? [I: $i] :
                                        ( ( r1_tarski @ I @ ( k2_xboole_0 @ G @ H ) )
                                        & ( m1_connsp_2 @ I @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                           => ( ( ( E = D )
                                & ( F = D ) )
                             => ! [G: $i] :
                                  ( ( m1_connsp_2 @ G @ B @ E )
                                 => ! [H: $i] :
                                      ( ( m1_connsp_2 @ H @ C @ F )
                                     => ? [I: $i] :
                                          ( ( r1_tarski @ I @ ( k2_xboole_0 @ G @ H ) )
                                          & ( m1_connsp_2 @ I @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_connsp_2 @ sk_G @ sk_B @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_E = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_E = sk_F ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_E ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_E = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t20_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ( ( ( E = D )
                              & ( F = D ) )
                           => ! [G: $i] :
                                ( ( m1_connsp_2 @ G @ B @ E )
                               => ! [H: $i] :
                                    ( ( m1_connsp_2 @ H @ C @ F )
                                   => ? [I: $i] :
                                        ( ( r1_tarski @ I @ ( k2_xboole_0 @ G @ H ) )
                                        & ( r2_hidden @ D @ I )
                                        & ( v3_pre_topc @ I @ ( k1_tsep_1 @ A @ B @ C ) )
                                        & ( m1_subset_1 @ I @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_connsp_2 @ X12 @ X10 @ X11 )
      | ( r1_tarski @ ( sk_I @ X12 @ X13 @ X9 @ X10 @ X7 @ X8 ) @ ( k2_xboole_0 @ X13 @ X12 ) )
      | ~ ( m1_connsp_2 @ X13 @ X7 @ X14 )
      | ( X11 != X9 )
      | ( X14 != X9 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t20_tmap_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_connsp_2 @ X13 @ X7 @ X9 )
      | ( r1_tarski @ ( sk_I @ X12 @ X13 @ X9 @ X10 @ X7 @ X8 ) @ ( k2_xboole_0 @ X13 @ X12 ) )
      | ~ ( m1_connsp_2 @ X12 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( r1_tarski @ ( sk_I @ X0 @ X1 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_B @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_E = sk_F ),
    inference('sup+',[status(thm)],['3','4'])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( r1_tarski @ ( sk_I @ X0 @ X1 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_B @ sk_E )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','16','17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( r1_tarski @ ( sk_I @ sk_H @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_H ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_G @ sk_H ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','22'])).

thf('24',plain,(
    m1_connsp_2 @ sk_G @ sk_B @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_E ),
    inference(demod,[status(thm)],['2','5'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_connsp_2 @ X12 @ X10 @ X11 )
      | ( r2_hidden @ X9 @ ( sk_I @ X12 @ X13 @ X9 @ X10 @ X7 @ X8 ) )
      | ~ ( m1_connsp_2 @ X13 @ X7 @ X14 )
      | ( X11 != X9 )
      | ( X14 != X9 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t20_tmap_1])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_connsp_2 @ X13 @ X7 @ X9 )
      | ( r2_hidden @ X9 @ ( sk_I @ X12 @ X13 @ X9 @ X10 @ X7 @ X8 ) )
      | ~ ( m1_connsp_2 @ X12 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( r2_hidden @ sk_E @ ( sk_I @ X0 @ X1 @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_B @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( r2_hidden @ sk_E @ ( sk_I @ X0 @ X1 @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_B @ sk_E )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( r2_hidden @ sk_E @ ( sk_I @ sk_H @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_E @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X3 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    m1_connsp_2 @ sk_G @ sk_B @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_E ),
    inference(demod,[status(thm)],['2','5'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_connsp_2 @ X12 @ X10 @ X11 )
      | ( v3_pre_topc @ ( sk_I @ X12 @ X13 @ X9 @ X10 @ X7 @ X8 ) @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
      | ~ ( m1_connsp_2 @ X13 @ X7 @ X14 )
      | ( X11 != X9 )
      | ( X14 != X9 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t20_tmap_1])).

thf('60',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_connsp_2 @ X13 @ X7 @ X9 )
      | ( v3_pre_topc @ ( sk_I @ X12 @ X13 @ X9 @ X10 @ X7 @ X8 ) @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
      | ~ ( m1_connsp_2 @ X12 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( v3_pre_topc @ ( sk_I @ X0 @ X1 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_B @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( v3_pre_topc @ ( sk_I @ X0 @ X1 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_B @ sk_E )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( v3_pre_topc @ ( sk_I @ sk_H @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v3_pre_topc @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','69'])).

thf('71',plain,(
    m1_connsp_2 @ sk_G @ sk_B @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_E ),
    inference(demod,[status(thm)],['2','5'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('74',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_connsp_2 @ X12 @ X10 @ X11 )
      | ( m1_subset_1 @ ( sk_I @ X12 @ X13 @ X9 @ X10 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) ) )
      | ~ ( m1_connsp_2 @ X13 @ X7 @ X14 )
      | ( X11 != X9 )
      | ( X14 != X9 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t20_tmap_1])).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_connsp_2 @ X13 @ X7 @ X9 )
      | ( m1_subset_1 @ ( sk_I @ X12 @ X13 @ X9 @ X10 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) ) )
      | ~ ( m1_connsp_2 @ X12 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( m1_subset_1 @ ( sk_I @ X0 @ X1 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_B @ sk_E )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('79',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( m1_subset_1 @ ( sk_I @ X0 @ X1 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_B @ sk_E )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( m1_subset_1 @ ( sk_I @ sk_H @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','84'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('86',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ( m1_connsp_2 @ X18 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['55','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['49','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_E )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_E )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_connsp_2 @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ sk_G @ sk_H ) )
      | ~ ( m1_connsp_2 @ X21 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_E = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ sk_G @ sk_H ) )
      | ~ ( m1_connsp_2 @ X21 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_E ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ ( sk_I @ sk_H @ sk_G @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X3 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','114'])).


%------------------------------------------------------------------------------
