%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ThmyQT6464

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:11 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  137 (1590 expanded)
%              Number of leaves         :   26 ( 461 expanded)
%              Depth                    :   22
%              Number of atoms          : 1266 (24446 expanded)
%              Number of equality atoms :   31 (1015 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t25_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( C = D )
                      & ( v2_tex_2 @ C @ A ) )
                   => ( v2_tex_2 @ D @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                        & ( C = D )
                        & ( v2_tex_2 @ C @ A ) )
                     => ( v2_tex_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('23',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf(d5_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    ~ ( v2_tex_2 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ( m1_subset_1 @ ( sk_D @ X24 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( sk_C @ X22 @ X23 ) @ X22 )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('62',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('66',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X23 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ X25 )
       != ( sk_C @ X22 @ X23 ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( v2_tex_2 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( sk_D @ X24 @ X22 @ X23 ) )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
      = ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['60','61'])).

thf('83',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
    = ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( ( sk_C @ sk_C_1 @ sk_B )
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','83'])).

thf('85',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('87',plain,(
    ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','62'])).

thf('89',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','62'])).

thf('90',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ X17 @ X18 )
      | ( X17 != X15 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('92',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v3_pre_topc @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('97',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ( v3_pre_topc @ ( sk_D @ X24 @ X22 @ X23 ) @ X23 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['60','61'])).

thf('105',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['27','28'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['95','105','106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['87','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ThmyQT6464
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:40:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.89/1.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.17  % Solved by: fo/fo7.sh
% 0.89/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.17  % done 763 iterations in 0.722s
% 0.89/1.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.17  % SZS output start Refutation
% 0.89/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.17  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.89/1.17  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.89/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.17  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.89/1.17  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.89/1.17  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.89/1.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.89/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.17  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.89/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.17  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.89/1.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.89/1.17  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.89/1.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.89/1.17  thf(t25_tex_2, conjecture,
% 0.89/1.17    (![A:$i]:
% 0.89/1.17     ( ( l1_pre_topc @ A ) =>
% 0.89/1.17       ( ![B:$i]:
% 0.89/1.17         ( ( l1_pre_topc @ B ) =>
% 0.89/1.17           ( ![C:$i]:
% 0.89/1.17             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.17               ( ![D:$i]:
% 0.89/1.17                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.89/1.17                   ( ( ( ( g1_pre_topc @
% 0.89/1.17                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.89/1.17                         ( g1_pre_topc @
% 0.89/1.17                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.89/1.17                       ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.89/1.17                     ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.89/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.17    (~( ![A:$i]:
% 0.89/1.17        ( ( l1_pre_topc @ A ) =>
% 0.89/1.17          ( ![B:$i]:
% 0.89/1.17            ( ( l1_pre_topc @ B ) =>
% 0.89/1.17              ( ![C:$i]:
% 0.89/1.17                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.17                  ( ![D:$i]:
% 0.89/1.17                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.89/1.17                      ( ( ( ( g1_pre_topc @
% 0.89/1.17                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.89/1.17                            ( g1_pre_topc @
% 0.89/1.17                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.89/1.17                          ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.89/1.17                        ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.89/1.17    inference('cnf.neg', [status(esa)], [t25_tex_2])).
% 0.89/1.17  thf('0', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf(t2_tsep_1, axiom,
% 0.89/1.17    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.89/1.17  thf('1', plain,
% 0.89/1.17      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.89/1.17      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.89/1.17  thf(t65_pre_topc, axiom,
% 0.89/1.17    (![A:$i]:
% 0.89/1.17     ( ( l1_pre_topc @ A ) =>
% 0.89/1.17       ( ![B:$i]:
% 0.89/1.17         ( ( l1_pre_topc @ B ) =>
% 0.89/1.17           ( ( m1_pre_topc @ A @ B ) <=>
% 0.89/1.17             ( m1_pre_topc @
% 0.89/1.17               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.89/1.17  thf('2', plain,
% 0.89/1.17      (![X13 : $i, X14 : $i]:
% 0.89/1.17         (~ (l1_pre_topc @ X13)
% 0.89/1.17          | ~ (m1_pre_topc @ X14 @ X13)
% 0.89/1.17          | (m1_pre_topc @ X14 @ 
% 0.89/1.17             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.89/1.17          | ~ (l1_pre_topc @ X14))),
% 0.89/1.17      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.89/1.17  thf('3', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (l1_pre_topc @ X0)
% 0.89/1.17          | ~ (l1_pre_topc @ X0)
% 0.89/1.17          | (m1_pre_topc @ X0 @ 
% 0.89/1.17             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.89/1.17          | ~ (l1_pre_topc @ X0))),
% 0.89/1.17      inference('sup-', [status(thm)], ['1', '2'])).
% 0.89/1.17  thf('4', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((m1_pre_topc @ X0 @ 
% 0.89/1.17           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.89/1.17          | ~ (l1_pre_topc @ X0))),
% 0.89/1.17      inference('simplify', [status(thm)], ['3'])).
% 0.89/1.17  thf('5', plain,
% 0.89/1.17      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.17         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf(t59_pre_topc, axiom,
% 0.89/1.17    (![A:$i]:
% 0.89/1.17     ( ( l1_pre_topc @ A ) =>
% 0.89/1.17       ( ![B:$i]:
% 0.89/1.17         ( ( m1_pre_topc @
% 0.89/1.17             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.89/1.17           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.89/1.17  thf('6', plain,
% 0.89/1.17      (![X11 : $i, X12 : $i]:
% 0.89/1.17         (~ (m1_pre_topc @ X11 @ 
% 0.89/1.17             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.89/1.17          | (m1_pre_topc @ X11 @ X12)
% 0.89/1.17          | ~ (l1_pre_topc @ X12))),
% 0.89/1.17      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.89/1.17  thf('7', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_pre_topc @ X0 @ 
% 0.89/1.17             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.89/1.17          | ~ (l1_pre_topc @ sk_B)
% 0.89/1.17          | (m1_pre_topc @ X0 @ sk_B))),
% 0.89/1.17      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.17  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('9', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_pre_topc @ X0 @ 
% 0.89/1.17             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.89/1.17          | (m1_pre_topc @ X0 @ sk_B))),
% 0.89/1.17      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.17  thf('10', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.89/1.17      inference('sup-', [status(thm)], ['4', '9'])).
% 0.89/1.17  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('12', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.89/1.17      inference('demod', [status(thm)], ['10', '11'])).
% 0.89/1.17  thf(t1_tsep_1, axiom,
% 0.89/1.17    (![A:$i]:
% 0.89/1.17     ( ( l1_pre_topc @ A ) =>
% 0.89/1.17       ( ![B:$i]:
% 0.89/1.17         ( ( m1_pre_topc @ B @ A ) =>
% 0.89/1.17           ( m1_subset_1 @
% 0.89/1.17             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.89/1.17  thf('13', plain,
% 0.89/1.17      (![X19 : $i, X20 : $i]:
% 0.89/1.17         (~ (m1_pre_topc @ X19 @ X20)
% 0.89/1.17          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.89/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.89/1.17          | ~ (l1_pre_topc @ X20))),
% 0.89/1.17      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.89/1.17  thf('14', plain,
% 0.89/1.17      ((~ (l1_pre_topc @ sk_B)
% 0.89/1.17        | (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.17           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.89/1.17      inference('sup-', [status(thm)], ['12', '13'])).
% 0.89/1.17  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('16', plain,
% 0.89/1.17      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.89/1.17      inference('demod', [status(thm)], ['14', '15'])).
% 0.89/1.17  thf(t3_subset, axiom,
% 0.89/1.17    (![A:$i,B:$i]:
% 0.89/1.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.89/1.17  thf('17', plain,
% 0.89/1.17      (![X3 : $i, X4 : $i]:
% 0.89/1.17         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.89/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.89/1.17  thf('18', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.89/1.17      inference('sup-', [status(thm)], ['16', '17'])).
% 0.89/1.17  thf(d10_xboole_0, axiom,
% 0.89/1.17    (![A:$i,B:$i]:
% 0.89/1.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.17  thf('19', plain,
% 0.89/1.17      (![X0 : $i, X2 : $i]:
% 0.89/1.17         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.17  thf('20', plain,
% 0.89/1.17      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.17        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('sup-', [status(thm)], ['18', '19'])).
% 0.89/1.17  thf('21', plain,
% 0.89/1.17      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.17         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('22', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((m1_pre_topc @ X0 @ 
% 0.89/1.17           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.89/1.17          | ~ (l1_pre_topc @ X0))),
% 0.89/1.17      inference('simplify', [status(thm)], ['3'])).
% 0.89/1.17  thf('23', plain,
% 0.89/1.17      (((m1_pre_topc @ sk_B @ 
% 0.89/1.17         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.89/1.17        | ~ (l1_pre_topc @ sk_B))),
% 0.89/1.17      inference('sup+', [status(thm)], ['21', '22'])).
% 0.89/1.17  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('25', plain,
% 0.89/1.17      ((m1_pre_topc @ sk_B @ 
% 0.89/1.17        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.89/1.17      inference('demod', [status(thm)], ['23', '24'])).
% 0.89/1.17  thf('26', plain,
% 0.89/1.17      (![X11 : $i, X12 : $i]:
% 0.89/1.17         (~ (m1_pre_topc @ X11 @ 
% 0.89/1.17             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.89/1.17          | (m1_pre_topc @ X11 @ X12)
% 0.89/1.17          | ~ (l1_pre_topc @ X12))),
% 0.89/1.17      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.89/1.17  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.89/1.17      inference('sup-', [status(thm)], ['25', '26'])).
% 0.89/1.17  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.89/1.17      inference('demod', [status(thm)], ['27', '28'])).
% 0.89/1.17  thf('30', plain,
% 0.89/1.17      (![X19 : $i, X20 : $i]:
% 0.89/1.17         (~ (m1_pre_topc @ X19 @ X20)
% 0.89/1.17          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.89/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.89/1.17          | ~ (l1_pre_topc @ X20))),
% 0.89/1.17      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.89/1.17  thf('31', plain,
% 0.89/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.17        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.89/1.17           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.89/1.17      inference('sup-', [status(thm)], ['29', '30'])).
% 0.89/1.17  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('33', plain,
% 0.89/1.17      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.89/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('demod', [status(thm)], ['31', '32'])).
% 0.89/1.17  thf('34', plain,
% 0.89/1.17      (![X3 : $i, X4 : $i]:
% 0.89/1.17         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.89/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.89/1.17  thf('35', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.89/1.17      inference('sup-', [status(thm)], ['33', '34'])).
% 0.89/1.17  thf('36', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['20', '35'])).
% 0.89/1.17  thf(d5_tex_2, axiom,
% 0.89/1.17    (![A:$i]:
% 0.89/1.17     ( ( l1_pre_topc @ A ) =>
% 0.89/1.17       ( ![B:$i]:
% 0.89/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.17           ( ( v2_tex_2 @ B @ A ) <=>
% 0.89/1.17             ( ![C:$i]:
% 0.89/1.17               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.17                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.89/1.17                      ( ![D:$i]:
% 0.89/1.17                        ( ( m1_subset_1 @
% 0.89/1.17                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.17                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.89/1.17                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.89/1.17                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.89/1.17  thf('37', plain,
% 0.89/1.17      (![X22 : $i, X23 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | (m1_subset_1 @ (sk_C @ X22 @ X23) @ 
% 0.89/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | (v2_tex_2 @ X22 @ X23)
% 0.89/1.17          | ~ (l1_pre_topc @ X23))),
% 0.89/1.17      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.89/1.17  thf('38', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (l1_pre_topc @ sk_B)
% 0.89/1.17          | (v2_tex_2 @ X0 @ sk_B)
% 0.89/1.17          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.89/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.89/1.17      inference('sup-', [status(thm)], ['36', '37'])).
% 0.89/1.17  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('40', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['20', '35'])).
% 0.89/1.17  thf('41', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | (v2_tex_2 @ X0 @ sk_B)
% 0.89/1.17          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.89/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.89/1.17      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.89/1.17  thf('42', plain,
% 0.89/1.17      (((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.89/1.17         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17        | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.89/1.17      inference('sup-', [status(thm)], ['0', '41'])).
% 0.89/1.17  thf('43', plain, (~ (v2_tex_2 @ sk_D_1 @ sk_B)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('44', plain, (((sk_C_1) = (sk_D_1))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('45', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.89/1.17      inference('demod', [status(thm)], ['43', '44'])).
% 0.89/1.17  thf('46', plain,
% 0.89/1.17      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.89/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('clc', [status(thm)], ['42', '45'])).
% 0.89/1.17  thf('47', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('48', plain,
% 0.89/1.17      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | ~ (v2_tex_2 @ X22 @ X23)
% 0.89/1.17          | (m1_subset_1 @ (sk_D @ X24 @ X22 @ X23) @ 
% 0.89/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | ~ (r1_tarski @ X24 @ X22)
% 0.89/1.17          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | ~ (l1_pre_topc @ X23))),
% 0.89/1.17      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.89/1.17  thf('49', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (l1_pre_topc @ sk_A)
% 0.89/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.89/1.17          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.89/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.89/1.17      inference('sup-', [status(thm)], ['47', '48'])).
% 0.89/1.17  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('51', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('52', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.89/1.17          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.89/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.89/1.17      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.89/1.17  thf('53', plain,
% 0.89/1.17      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.89/1.17         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.89/1.17      inference('sup-', [status(thm)], ['46', '52'])).
% 0.89/1.17  thf('54', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('55', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['20', '35'])).
% 0.89/1.17  thf('56', plain,
% 0.89/1.17      (![X22 : $i, X23 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | (r1_tarski @ (sk_C @ X22 @ X23) @ X22)
% 0.89/1.17          | (v2_tex_2 @ X22 @ X23)
% 0.89/1.17          | ~ (l1_pre_topc @ X23))),
% 0.89/1.17      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.89/1.17  thf('57', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (l1_pre_topc @ sk_B)
% 0.89/1.17          | (v2_tex_2 @ X0 @ sk_B)
% 0.89/1.17          | (r1_tarski @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.89/1.17      inference('sup-', [status(thm)], ['55', '56'])).
% 0.89/1.17  thf('58', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('59', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | (v2_tex_2 @ X0 @ sk_B)
% 0.89/1.17          | (r1_tarski @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.89/1.17      inference('demod', [status(thm)], ['57', '58'])).
% 0.89/1.17  thf('60', plain,
% 0.89/1.17      (((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.89/1.17        | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.89/1.17      inference('sup-', [status(thm)], ['54', '59'])).
% 0.89/1.17  thf('61', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.89/1.17      inference('demod', [status(thm)], ['43', '44'])).
% 0.89/1.17  thf('62', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.89/1.17      inference('clc', [status(thm)], ['60', '61'])).
% 0.89/1.17  thf('63', plain,
% 0.89/1.17      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.89/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('demod', [status(thm)], ['53', '62'])).
% 0.89/1.17  thf('64', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('65', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['20', '35'])).
% 0.89/1.17  thf('66', plain,
% 0.89/1.17      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | ~ (v3_pre_topc @ X25 @ X23)
% 0.89/1.17          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ X25)
% 0.89/1.17              != (sk_C @ X22 @ X23))
% 0.89/1.17          | (v2_tex_2 @ X22 @ X23)
% 0.89/1.17          | ~ (l1_pre_topc @ X23))),
% 0.89/1.17      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.89/1.17  thf('67', plain,
% 0.89/1.17      (![X0 : $i, X1 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (l1_pre_topc @ sk_B)
% 0.89/1.17          | (v2_tex_2 @ X0 @ sk_B)
% 0.89/1.17          | ((k9_subset_1 @ (u1_struct_0 @ sk_B) @ X0 @ X1)
% 0.89/1.17              != (sk_C @ X0 @ sk_B))
% 0.89/1.17          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.89/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.89/1.17      inference('sup-', [status(thm)], ['65', '66'])).
% 0.89/1.17  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('69', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['20', '35'])).
% 0.89/1.17  thf('70', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['20', '35'])).
% 0.89/1.17  thf('71', plain,
% 0.89/1.17      (![X0 : $i, X1 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | (v2_tex_2 @ X0 @ sk_B)
% 0.89/1.17          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X1)
% 0.89/1.17              != (sk_C @ X0 @ sk_B))
% 0.89/1.17          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.89/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.89/1.17      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.89/1.17  thf('72', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.89/1.17          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 0.89/1.17              != (sk_C @ sk_C_1 @ sk_B))
% 0.89/1.17          | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.89/1.17      inference('sup-', [status(thm)], ['64', '71'])).
% 0.89/1.17  thf('73', plain,
% 0.89/1.17      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.89/1.17        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.89/1.17            (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.89/1.17            != (sk_C @ sk_C_1 @ sk_B))
% 0.89/1.17        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.89/1.17             sk_B))),
% 0.89/1.17      inference('sup-', [status(thm)], ['63', '72'])).
% 0.89/1.17  thf('74', plain,
% 0.89/1.17      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.89/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('clc', [status(thm)], ['42', '45'])).
% 0.89/1.17  thf('75', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('76', plain,
% 0.89/1.17      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | ~ (v2_tex_2 @ X22 @ X23)
% 0.89/1.17          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.89/1.17              (sk_D @ X24 @ X22 @ X23)) = (X24))
% 0.89/1.17          | ~ (r1_tarski @ X24 @ X22)
% 0.89/1.17          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | ~ (l1_pre_topc @ X23))),
% 0.89/1.17      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.89/1.17  thf('77', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (l1_pre_topc @ sk_A)
% 0.89/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.89/1.17          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.89/1.17              (sk_D @ X0 @ sk_C_1 @ sk_A)) = (X0))
% 0.89/1.17          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.89/1.17      inference('sup-', [status(thm)], ['75', '76'])).
% 0.89/1.17  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('79', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('80', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.89/1.17          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.89/1.17              (sk_D @ X0 @ sk_C_1 @ sk_A)) = (X0)))),
% 0.89/1.17      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.89/1.17  thf('81', plain,
% 0.89/1.17      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.89/1.17          (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.89/1.17          = (sk_C @ sk_C_1 @ sk_B))
% 0.89/1.17        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.89/1.17      inference('sup-', [status(thm)], ['74', '80'])).
% 0.89/1.17  thf('82', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.89/1.17      inference('clc', [status(thm)], ['60', '61'])).
% 0.89/1.17  thf('83', plain,
% 0.89/1.17      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.89/1.17         (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.89/1.17         = (sk_C @ sk_C_1 @ sk_B))),
% 0.89/1.17      inference('demod', [status(thm)], ['81', '82'])).
% 0.89/1.17  thf('84', plain,
% 0.89/1.17      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.89/1.17        | ((sk_C @ sk_C_1 @ sk_B) != (sk_C @ sk_C_1 @ sk_B))
% 0.89/1.17        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.89/1.17             sk_B))),
% 0.89/1.17      inference('demod', [status(thm)], ['73', '83'])).
% 0.89/1.17  thf('85', plain,
% 0.89/1.17      ((~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)
% 0.89/1.17        | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.89/1.17      inference('simplify', [status(thm)], ['84'])).
% 0.89/1.17  thf('86', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.89/1.17      inference('demod', [status(thm)], ['43', '44'])).
% 0.89/1.17  thf('87', plain,
% 0.89/1.17      (~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)),
% 0.89/1.17      inference('clc', [status(thm)], ['85', '86'])).
% 0.89/1.17  thf('88', plain,
% 0.89/1.17      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.89/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('demod', [status(thm)], ['53', '62'])).
% 0.89/1.17  thf('89', plain,
% 0.89/1.17      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.89/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('demod', [status(thm)], ['53', '62'])).
% 0.89/1.17  thf('90', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['20', '35'])).
% 0.89/1.17  thf(t33_tops_2, axiom,
% 0.89/1.17    (![A:$i]:
% 0.89/1.17     ( ( l1_pre_topc @ A ) =>
% 0.89/1.17       ( ![B:$i]:
% 0.89/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.17           ( ![C:$i]:
% 0.89/1.17             ( ( m1_pre_topc @ C @ A ) =>
% 0.89/1.17               ( ( v3_pre_topc @ B @ A ) =>
% 0.89/1.17                 ( ![D:$i]:
% 0.89/1.17                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.89/1.17                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.89/1.17  thf('91', plain,
% 0.89/1.17      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.89/1.17          | ~ (v3_pre_topc @ X15 @ X16)
% 0.89/1.17          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.89/1.17          | (v3_pre_topc @ X17 @ X18)
% 0.89/1.17          | ((X17) != (X15))
% 0.89/1.17          | ~ (m1_pre_topc @ X18 @ X16)
% 0.89/1.17          | ~ (l1_pre_topc @ X16))),
% 0.89/1.17      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.89/1.17  thf('92', plain,
% 0.89/1.17      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.89/1.17         (~ (l1_pre_topc @ X16)
% 0.89/1.17          | ~ (m1_pre_topc @ X18 @ X16)
% 0.89/1.17          | (v3_pre_topc @ X15 @ X18)
% 0.89/1.17          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.89/1.17          | ~ (v3_pre_topc @ X15 @ X16)
% 0.89/1.17          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.89/1.17      inference('simplify', [status(thm)], ['91'])).
% 0.89/1.17  thf('93', plain,
% 0.89/1.17      (![X0 : $i, X1 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.89/1.17          | ~ (v3_pre_topc @ X0 @ X1)
% 0.89/1.17          | (v3_pre_topc @ X0 @ sk_B)
% 0.89/1.17          | ~ (m1_pre_topc @ sk_B @ X1)
% 0.89/1.17          | ~ (l1_pre_topc @ X1))),
% 0.89/1.17      inference('sup-', [status(thm)], ['90', '92'])).
% 0.89/1.17  thf('94', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (l1_pre_topc @ X0)
% 0.89/1.17          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.89/1.17          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.89/1.17             sk_B)
% 0.89/1.17          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.89/1.17               X0)
% 0.89/1.17          | ~ (m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.89/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.89/1.17      inference('sup-', [status(thm)], ['89', '93'])).
% 0.89/1.17  thf('95', plain,
% 0.89/1.17      ((~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)
% 0.89/1.17        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)
% 0.89/1.17        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.89/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.17      inference('sup-', [status(thm)], ['88', '94'])).
% 0.89/1.17  thf('96', plain,
% 0.89/1.17      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.89/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('clc', [status(thm)], ['42', '45'])).
% 0.89/1.17  thf('97', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('98', plain,
% 0.89/1.17      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | ~ (v2_tex_2 @ X22 @ X23)
% 0.89/1.17          | (v3_pre_topc @ (sk_D @ X24 @ X22 @ X23) @ X23)
% 0.89/1.17          | ~ (r1_tarski @ X24 @ X22)
% 0.89/1.17          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.89/1.17          | ~ (l1_pre_topc @ X23))),
% 0.89/1.17      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.89/1.17  thf('99', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (l1_pre_topc @ sk_A)
% 0.89/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.89/1.17          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A)
% 0.89/1.17          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.89/1.17      inference('sup-', [status(thm)], ['97', '98'])).
% 0.89/1.17  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('101', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('102', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.17          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.89/1.17          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.89/1.17  thf('103', plain,
% 0.89/1.17      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)
% 0.89/1.17        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.89/1.17      inference('sup-', [status(thm)], ['96', '102'])).
% 0.89/1.17  thf('104', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.89/1.17      inference('clc', [status(thm)], ['60', '61'])).
% 0.89/1.17  thf('105', plain,
% 0.89/1.17      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)),
% 0.89/1.17      inference('demod', [status(thm)], ['103', '104'])).
% 0.89/1.17  thf('106', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.89/1.17      inference('demod', [status(thm)], ['27', '28'])).
% 0.89/1.17  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('108', plain,
% 0.89/1.17      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)),
% 0.89/1.17      inference('demod', [status(thm)], ['95', '105', '106', '107'])).
% 0.89/1.17  thf('109', plain, ($false), inference('demod', [status(thm)], ['87', '108'])).
% 0.89/1.17  
% 0.89/1.17  % SZS output end Refutation
% 0.89/1.17  
% 1.01/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
