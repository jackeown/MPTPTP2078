%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3sjW2BIVM3

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 466 expanded)
%              Number of leaves         :   36 ( 145 expanded)
%              Depth                    :   28
%              Number of atoms          : 2008 (14978 expanded)
%              Number of equality atoms :   11 ( 217 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t67_tmap_1,conjecture,(
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
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

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
                      & ( v1_tsep_1 @ D @ B )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ( ( E = F )
                             => ( ( r1_tmap_1 @ B @ A @ C @ E )
                              <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ( m1_connsp_2 @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 @ X14 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15','24'])).

thf('26',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ( r1_tarski @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
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
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('45',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('64',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['57'])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( r1_tmap_1 @ X22 @ X24 @ ( k2_tmap_1 @ X21 @ X24 @ X25 @ X22 ) @ X23 )
      | ( X26 != X23 )
      | ~ ( r1_tmap_1 @ X21 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('67',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_tmap_1 @ X21 @ X24 @ X25 @ X23 )
      | ( r1_tmap_1 @ X22 @ X24 @ ( k2_tmap_1 @ X21 @ X24 @ X25 @ X22 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['63','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['61'])).

thf('83',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['57'])).

thf('93',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['62','91','92'])).

thf('94',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['60','93'])).

thf('95',plain,(
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

thf('96',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r1_tarski @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_connsp_2 @ X30 @ X27 @ X29 )
      | ( X29 != X31 )
      | ~ ( r1_tmap_1 @ X28 @ X32 @ ( k2_tmap_1 @ X27 @ X32 @ X33 @ X28 ) @ X31 )
      | ( r1_tmap_1 @ X27 @ X32 @ X33 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('97',plain,(
    ! [X27: $i,X28: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X27 @ X32 @ X33 @ X31 )
      | ~ ( r1_tmap_1 @ X28 @ X32 @ ( k2_tmap_1 @ X27 @ X32 @ X33 @ X28 ) @ X31 )
      | ~ ( m1_connsp_2 @ X30 @ X27 @ X31 )
      | ~ ( r1_tarski @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
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
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
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
    inference(demod,[status(thm)],['98','99','100','101','102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('108',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['43','111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['61'])).

thf('117',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['62','91'])).

thf('118',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('120',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('123',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['124','125'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('127',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('128',plain,(
    l1_struct_0 @ sk_D_1 ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['121','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['0','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3sjW2BIVM3
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 101 iterations in 0.066s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.54  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(t67_tmap_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.54             ( l1_pre_topc @ B ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54                 ( m1_subset_1 @
% 0.21/0.54                   C @ 
% 0.21/0.54                   ( k1_zfmisc_1 @
% 0.21/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.54                     ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.54                   ( ![E:$i]:
% 0.21/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                       ( ![F:$i]:
% 0.21/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.54                           ( ( ( E ) = ( F ) ) =>
% 0.21/0.54                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.54                               ( r1_tmap_1 @
% 0.21/0.54                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.54                ( l1_pre_topc @ B ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54                    ( v1_funct_2 @
% 0.21/0.54                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54                    ( m1_subset_1 @
% 0.21/0.54                      C @ 
% 0.21/0.54                      ( k1_zfmisc_1 @
% 0.21/0.54                        ( k2_zfmisc_1 @
% 0.21/0.54                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.54                  ( ![D:$i]:
% 0.21/0.54                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.54                        ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.54                      ( ![E:$i]:
% 0.21/0.54                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                          ( ![F:$i]:
% 0.21/0.54                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.54                              ( ( ( E ) = ( F ) ) =>
% 0.21/0.54                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.54                                  ( r1_tmap_1 @
% 0.21/0.54                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.21/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('2', plain, (((sk_E) = (sk_F))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf(t2_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ X0 @ X1)
% 0.21/0.54          | (v1_xboole_0 @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('6', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t1_tsep_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( m1_subset_1 @
% 0.21/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X19 @ X20)
% 0.21/0.54          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.54          | ~ (l1_pre_topc @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf(t9_connsp_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.54                      ( ![D:$i]:
% 0.21/0.54                        ( ( m1_subset_1 @
% 0.21/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.21/0.54                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.54          | ~ (v3_pre_topc @ X12 @ X13)
% 0.21/0.54          | (m1_connsp_2 @ (sk_D @ X14 @ X12 @ X13) @ X13 @ X14)
% 0.21/0.54          | ~ (r2_hidden @ X14 @ X12)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.54          | ~ (l1_pre_topc @ X13)
% 0.21/0.54          | ~ (v2_pre_topc @ X13)
% 0.21/0.54          | (v2_struct_0 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             sk_B @ X0)
% 0.21/0.54          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf(t16_tsep_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.54                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.54          | ((X18) != (u1_struct_0 @ X16))
% 0.21/0.54          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.21/0.54          | ~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.54          | (v3_pre_topc @ X18 @ X17)
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.54          | ~ (l1_pre_topc @ X17)
% 0.21/0.54          | ~ (v2_pre_topc @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ X17)
% 0.21/0.54          | ~ (l1_pre_topc @ X17)
% 0.21/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.21/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.54          | (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.21/0.54          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.21/0.54          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.21/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.54        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.21/0.54        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.54  thf('20', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('21', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('24', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             sk_B @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['13', '14', '15', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.21/0.54         sk_E)
% 0.21/0.54        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '25'])).
% 0.21/0.54  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54           sk_B @ sk_E))),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54           sk_B @ sk_E))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('31', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.54          | ~ (v3_pre_topc @ X12 @ X13)
% 0.21/0.54          | (r1_tarski @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 0.21/0.54          | ~ (r2_hidden @ X14 @ X12)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.54          | ~ (l1_pre_topc @ X13)
% 0.21/0.54          | ~ (v2_pre_topc @ X13)
% 0.21/0.54          | (v2_struct_0 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('35', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.54  thf('38', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54         (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '39'])).
% 0.21/0.54  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54           (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54           (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.54          | ~ (v3_pre_topc @ X12 @ X13)
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ X14 @ X12 @ X13) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.54          | ~ (r2_hidden @ X14 @ X12)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.54          | ~ (l1_pre_topc @ X13)
% 0.21/0.54          | ~ (v2_pre_topc @ X13)
% 0.21/0.54          | (v2_struct_0 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.54        | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '51'])).
% 0.21/0.54  thf('53', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54        | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (((m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.21/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.54      inference('split', [status(esa)], ['57'])).
% 0.21/0.54  thf('59', plain, (((sk_E) = (sk_F))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.54      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.21/0.54        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.21/0.54       ~
% 0.21/0.54       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.21/0.54      inference('split', [status(esa)], ['61'])).
% 0.21/0.54  thf('63', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.54      inference('split', [status(esa)], ['57'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t64_tmap_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.54             ( l1_pre_topc @ B ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54                 ( m1_subset_1 @
% 0.21/0.54                   C @ 
% 0.21/0.54                   ( k1_zfmisc_1 @
% 0.21/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.54                   ( ![E:$i]:
% 0.21/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                       ( ![F:$i]:
% 0.21/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.54                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.54                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.54                             ( r1_tmap_1 @
% 0.21/0.54                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X21)
% 0.21/0.54          | ~ (v2_pre_topc @ X21)
% 0.21/0.54          | ~ (l1_pre_topc @ X21)
% 0.21/0.54          | (v2_struct_0 @ X22)
% 0.21/0.54          | ~ (m1_pre_topc @ X22 @ X21)
% 0.21/0.54          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.21/0.54          | (r1_tmap_1 @ X22 @ X24 @ (k2_tmap_1 @ X21 @ X24 @ X25 @ X22) @ X23)
% 0.21/0.54          | ((X26) != (X23))
% 0.21/0.54          | ~ (r1_tmap_1 @ X21 @ X24 @ X25 @ X26)
% 0.21/0.54          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X21))
% 0.21/0.54          | ~ (m1_subset_1 @ X25 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))))
% 0.21/0.54          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))
% 0.21/0.54          | ~ (v1_funct_1 @ X25)
% 0.21/0.54          | ~ (l1_pre_topc @ X24)
% 0.21/0.54          | ~ (v2_pre_topc @ X24)
% 0.21/0.54          | (v2_struct_0 @ X24))),
% 0.21/0.54      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X24)
% 0.21/0.54          | ~ (v2_pre_topc @ X24)
% 0.21/0.54          | ~ (l1_pre_topc @ X24)
% 0.21/0.54          | ~ (v1_funct_1 @ X25)
% 0.21/0.54          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))
% 0.21/0.54          | ~ (m1_subset_1 @ X25 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))))
% 0.21/0.54          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.21/0.54          | ~ (r1_tmap_1 @ X21 @ X24 @ X25 @ X23)
% 0.21/0.54          | (r1_tmap_1 @ X22 @ X24 @ (k2_tmap_1 @ X21 @ X24 @ X25 @ X22) @ X23)
% 0.21/0.54          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.21/0.54          | ~ (m1_pre_topc @ X22 @ X21)
% 0.21/0.54          | (v2_struct_0 @ X22)
% 0.21/0.54          | ~ (l1_pre_topc @ X21)
% 0.21/0.54          | ~ (v2_pre_topc @ X21)
% 0.21/0.54          | (v2_struct_0 @ X21))),
% 0.21/0.54      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.21/0.54             X1)
% 0.21/0.54          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['65', '67'])).
% 0.21/0.54  thf('69', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.21/0.54             X1)
% 0.21/0.54          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['68', '69', '70', '71', '72', '73', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          ((v2_struct_0 @ sk_A)
% 0.21/0.54           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.54           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.54              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.21/0.54           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.54           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54           | (v2_struct_0 @ X0)
% 0.21/0.54           | (v2_struct_0 @ sk_B)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['64', '75'])).
% 0.21/0.54  thf('77', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          ((v2_struct_0 @ sk_A)
% 0.21/0.54           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.54              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.21/0.54           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.54           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54           | (v2_struct_0 @ X0)
% 0.21/0.54           | (v2_struct_0 @ sk_B)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.54      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_B)
% 0.21/0.54         | (v2_struct_0 @ sk_D_1)
% 0.21/0.54         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.54         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['63', '78'])).
% 0.21/0.54  thf('80', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_B)
% 0.21/0.54         | (v2_struct_0 @ sk_D_1)
% 0.21/0.54         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.54      inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.54  thf('82', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.54      inference('split', [status(esa)], ['61'])).
% 0.21/0.54  thf('83', plain, (((sk_E) = (sk_F))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.54      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.54  thf('85', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.21/0.54             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['81', '84'])).
% 0.21/0.54  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.21/0.54             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.54      inference('clc', [status(thm)], ['85', '86'])).
% 0.21/0.54  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('89', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_D_1))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.21/0.54             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.54      inference('clc', [status(thm)], ['87', '88'])).
% 0.21/0.54  thf('90', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.21/0.54       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.21/0.54       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.54      inference('split', [status(esa)], ['57'])).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['62', '91', '92'])).
% 0.21/0.54  thf('94', plain,
% 0.21/0.54      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.54        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['60', '93'])).
% 0.21/0.54  thf('95', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t65_tmap_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.54             ( l1_pre_topc @ B ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54                 ( m1_subset_1 @
% 0.21/0.54                   C @ 
% 0.21/0.54                   ( k1_zfmisc_1 @
% 0.21/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.54                   ( ![E:$i]:
% 0.21/0.54                     ( ( m1_subset_1 @
% 0.21/0.54                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54                       ( ![F:$i]:
% 0.21/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                           ( ![G:$i]:
% 0.21/0.54                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.54                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.54                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.21/0.54                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.54                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.54                                   ( r1_tmap_1 @
% 0.21/0.54                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('96', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X27)
% 0.21/0.54          | ~ (v2_pre_topc @ X27)
% 0.21/0.54          | ~ (l1_pre_topc @ X27)
% 0.21/0.54          | (v2_struct_0 @ X28)
% 0.21/0.54          | ~ (m1_pre_topc @ X28 @ X27)
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.21/0.54          | ~ (r1_tarski @ X30 @ (u1_struct_0 @ X28))
% 0.21/0.54          | ~ (m1_connsp_2 @ X30 @ X27 @ X29)
% 0.21/0.54          | ((X29) != (X31))
% 0.21/0.54          | ~ (r1_tmap_1 @ X28 @ X32 @ (k2_tmap_1 @ X27 @ X32 @ X33 @ X28) @ 
% 0.21/0.54               X31)
% 0.21/0.54          | (r1_tmap_1 @ X27 @ X32 @ X33 @ X29)
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X28))
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.54          | ~ (m1_subset_1 @ X33 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X32))))
% 0.21/0.54          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X32))
% 0.21/0.54          | ~ (v1_funct_1 @ X33)
% 0.21/0.54          | ~ (l1_pre_topc @ X32)
% 0.21/0.54          | ~ (v2_pre_topc @ X32)
% 0.21/0.54          | (v2_struct_0 @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.21/0.54  thf('97', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X32)
% 0.21/0.54          | ~ (v2_pre_topc @ X32)
% 0.21/0.54          | ~ (l1_pre_topc @ X32)
% 0.21/0.54          | ~ (v1_funct_1 @ X33)
% 0.21/0.54          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X32))
% 0.21/0.54          | ~ (m1_subset_1 @ X33 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X32))))
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X28))
% 0.21/0.54          | (r1_tmap_1 @ X27 @ X32 @ X33 @ X31)
% 0.21/0.54          | ~ (r1_tmap_1 @ X28 @ X32 @ (k2_tmap_1 @ X27 @ X32 @ X33 @ X28) @ 
% 0.21/0.54               X31)
% 0.21/0.54          | ~ (m1_connsp_2 @ X30 @ X27 @ X31)
% 0.21/0.54          | ~ (r1_tarski @ X30 @ (u1_struct_0 @ X28))
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X27))
% 0.21/0.54          | ~ (m1_pre_topc @ X28 @ X27)
% 0.21/0.54          | (v2_struct_0 @ X28)
% 0.21/0.54          | ~ (l1_pre_topc @ X27)
% 0.21/0.54          | ~ (v2_pre_topc @ X27)
% 0.21/0.54          | (v2_struct_0 @ X27))),
% 0.21/0.54      inference('simplify', [status(thm)], ['96'])).
% 0.21/0.54  thf('98', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.21/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['95', '97'])).
% 0.21/0.54  thf('99', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('101', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('102', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('105', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ X0)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.21/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['98', '99', '100', '101', '102', '103', '104'])).
% 0.21/0.54  thf('106', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.54          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.21/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.54          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ sk_D_1)
% 0.21/0.54          | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['94', '105'])).
% 0.21/0.54  thf('107', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('108', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('109', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('110', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.54          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.21/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54          | (v2_struct_0 @ sk_D_1)
% 0.21/0.54          | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.21/0.54  thf('111', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1)
% 0.21/0.54        | ~ (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             sk_B @ sk_E)
% 0.21/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['56', '110'])).
% 0.21/0.54  thf('112', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.54        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             sk_B @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1)
% 0.21/0.54        | (v2_struct_0 @ sk_B)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '111'])).
% 0.21/0.54  thf('113', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1)
% 0.21/0.54        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.54             sk_B @ sk_E)
% 0.21/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['112'])).
% 0.21/0.54  thf('114', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1)
% 0.21/0.54        | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '113'])).
% 0.21/0.54  thf('115', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1)
% 0.21/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['114'])).
% 0.21/0.54  thf('116', plain,
% 0.21/0.54      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.21/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.54      inference('split', [status(esa)], ['61'])).
% 0.21/0.54  thf('117', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['62', '91'])).
% 0.21/0.54  thf('118', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['116', '117'])).
% 0.21/0.54  thf('119', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1)
% 0.21/0.54        | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['115', '118'])).
% 0.21/0.54  thf(fc2_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('120', plain,
% 0.21/0.54      (![X5 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.21/0.54          | ~ (l1_struct_0 @ X5)
% 0.21/0.54          | (v2_struct_0 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.54  thf('121', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1)
% 0.21/0.54        | ~ (l1_struct_0 @ sk_D_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['119', '120'])).
% 0.21/0.54  thf('122', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_m1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.54  thf('123', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.54  thf('124', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['122', '123'])).
% 0.21/0.54  thf('125', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('126', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['124', '125'])).
% 0.21/0.54  thf(dt_l1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.54  thf('127', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.54  thf('128', plain, ((l1_struct_0 @ sk_D_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['126', '127'])).
% 0.21/0.54  thf('129', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['121', '128'])).
% 0.21/0.54  thf('130', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('simplify', [status(thm)], ['129'])).
% 0.21/0.54  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('132', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['130', '131'])).
% 0.21/0.54  thf('133', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('134', plain, ((v2_struct_0 @ sk_D_1)),
% 0.21/0.54      inference('clc', [status(thm)], ['132', '133'])).
% 0.21/0.54  thf('135', plain, ($false), inference('demod', [status(thm)], ['0', '134'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
