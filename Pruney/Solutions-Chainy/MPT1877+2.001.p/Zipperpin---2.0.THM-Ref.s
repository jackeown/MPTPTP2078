%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HKWfl7DvNy

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  153 (1982 expanded)
%              Number of leaves         :   24 ( 568 expanded)
%              Depth                    :   24
%              Number of atoms          : 1372 (30219 expanded)
%              Number of equality atoms :   45 (1275 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(t45_tex_2,conjecture,(
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
                      & ( v3_tex_2 @ C @ A ) )
                   => ( v3_tex_2 @ D @ B ) ) ) ) ) ) )).

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
                        & ( v3_tex_2 @ C @ A ) )
                     => ( v3_tex_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( m1_pre_topc @ X12 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
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
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('22',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_C @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    ~ ( v3_tex_2 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf(t25_tex_2,axiom,(
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

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_tex_2 @ X17 @ X16 )
      | ( X18 != X17 )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t25_tex_2])).

thf('50',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X19 )
      | ( v2_tex_2 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_tex_2 @ X1 @ sk_B )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('54',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X1 @ sk_B )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['51','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(eq_res,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_tex_2 @ X13 @ X14 )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    v2_tex_2 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['62','68'])).

thf('70',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_tex_2 @ X13 @ X14 )
      | ~ ( v2_tex_2 @ X15 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( X13 = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C_1 = X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C_1 = X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ~ ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ( sk_C_1
      = ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ X0 @ ( sk_C @ X0 @ sk_B ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ X0 @ ( sk_C @ X0 @ sk_B ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( r1_tarski @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ~ ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('86',plain,
    ( ( r1_tarski @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    v2_tex_2 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['62','68'])).

thf('88',plain,(
    r1_tarski @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A )
    | ( sk_C_1
      = ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('92',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( X13
       != ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( X0
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( X0
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( sk_C_1
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ~ ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('98',plain,
    ( ( sk_C_1
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    v2_tex_2 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['62','68'])).

thf('100',plain,(
    sk_C_1
 != ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['89','100'])).

thf('102',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','69'])).

thf('103',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('104',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X19 )
      | ( v2_tex_2 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v2_tex_2 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('107',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v2_tex_2 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('117',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( v2_tex_2 @ ( sk_C @ X13 @ X14 ) @ X14 )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( v2_tex_2 @ ( sk_C @ X0 @ sk_B ) @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( v2_tex_2 @ ( sk_C @ X0 @ sk_B ) @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,(
    ~ ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('123',plain,
    ( ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    v2_tex_2 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['62','68'])).

thf('125',plain,(
    v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['114','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['101','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HKWfl7DvNy
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:58:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 131 iterations in 0.062s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.54  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.54  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.54  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.54  thf(t45_tex_2, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( l1_pre_topc @ B ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54               ( ![D:$i]:
% 0.22/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.54                   ( ( ( ( g1_pre_topc @
% 0.22/0.54                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.54                         ( g1_pre_topc @
% 0.22/0.54                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.22/0.54                       ( ( C ) = ( D ) ) & ( v3_tex_2 @ C @ A ) ) =>
% 0.22/0.54                     ( v3_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( l1_pre_topc @ A ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( l1_pre_topc @ B ) =>
% 0.22/0.54              ( ![C:$i]:
% 0.22/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54                  ( ![D:$i]:
% 0.22/0.54                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.54                      ( ( ( ( g1_pre_topc @
% 0.22/0.54                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.54                            ( g1_pre_topc @
% 0.22/0.54                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.22/0.54                          ( ( C ) = ( D ) ) & ( v3_tex_2 @ C @ A ) ) =>
% 0.22/0.54                        ( v3_tex_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t45_tex_2])).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t2_tsep_1, axiom,
% 0.22/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X12 : $i]: ((m1_pre_topc @ X12 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.54  thf(t65_pre_topc, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( l1_pre_topc @ B ) =>
% 0.22/0.54           ( ( m1_pre_topc @ A @ B ) <=>
% 0.22/0.54             ( m1_pre_topc @
% 0.22/0.54               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X8)
% 0.22/0.54          | ~ (m1_pre_topc @ X9 @ X8)
% 0.22/0.54          | (m1_pre_topc @ X9 @ 
% 0.22/0.54             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.22/0.54          | ~ (l1_pre_topc @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (m1_pre_topc @ X0 @ 
% 0.22/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_pre_topc @ X0 @ 
% 0.22/0.54           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (((m1_pre_topc @ sk_B @ 
% 0.22/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.54      inference('sup+', [status(thm)], ['1', '5'])).
% 0.22/0.54  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      ((m1_pre_topc @ sk_B @ 
% 0.22/0.54        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.54  thf(t59_pre_topc, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_pre_topc @
% 0.22/0.54             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.22/0.54           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X6 @ 
% 0.22/0.54             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.22/0.54          | (m1_pre_topc @ X6 @ X7)
% 0.22/0.54          | ~ (l1_pre_topc @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.22/0.54  thf('10', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('12', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf(t1_tsep_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.54           ( m1_subset_1 @
% 0.22/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.54          | (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.54          | ~ (l1_pre_topc @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('18', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.54        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_pre_topc @ X0 @ 
% 0.22/0.54           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X6 @ 
% 0.22/0.54             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.22/0.54          | (m1_pre_topc @ X6 @ X7)
% 0.22/0.54          | ~ (l1_pre_topc @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X0 @ 
% 0.22/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54          | (m1_pre_topc @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X0 @ 
% 0.22/0.54             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.54          | (m1_pre_topc @ X0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.54  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['21', '26'])).
% 0.22/0.54  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('29', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.54          | (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.54          | ~ (l1_pre_topc @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.54  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('35', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf('36', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf(d7_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.54             ( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.54               ( ![C:$i]:
% 0.22/0.54                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.54                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (v2_tex_2 @ X13 @ X14)
% 0.22/0.54          | (m1_subset_1 @ (sk_C @ X13 @ X14) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | (v3_tex_2 @ X13 @ X14)
% 0.22/0.54          | ~ (l1_pre_topc @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54          | (v3_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.54  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('40', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v3_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((~ (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.22/0.54        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.22/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54        | (v3_tex_2 @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '41'])).
% 0.22/0.54  thf('43', plain, (~ (v3_tex_2 @ sk_D @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('44', plain, (((sk_C_1) = (sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('45', plain, (~ (v3_tex_2 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.22/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54        | ~ (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('clc', [status(thm)], ['42', '45'])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('48', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf(t25_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( l1_pre_topc @ B ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54               ( ![D:$i]:
% 0.22/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.54                   ( ( ( ( g1_pre_topc @
% 0.22/0.54                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.54                         ( g1_pre_topc @
% 0.22/0.54                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.22/0.54                       ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.22/0.54                     ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X16)
% 0.22/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.54          | (v2_tex_2 @ X17 @ X16)
% 0.22/0.54          | ((X18) != (X17))
% 0.22/0.54          | ~ (v2_tex_2 @ X18 @ X19)
% 0.22/0.54          | ((g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19))
% 0.22/0.54              != (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.22/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.54          | ~ (l1_pre_topc @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t25_tex_2])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X19)
% 0.22/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.54          | ((g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19))
% 0.22/0.54              != (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.22/0.54          | ~ (v2_tex_2 @ X17 @ X19)
% 0.22/0.54          | (v2_tex_2 @ X17 @ X16)
% 0.22/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.54          | ~ (l1_pre_topc @ X16))),
% 0.22/0.54      inference('simplify', [status(thm)], ['49'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.54            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_B)))
% 0.22/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.54          | (v2_tex_2 @ X1 @ sk_B)
% 0.22/0.54          | ~ (v2_tex_2 @ X1 @ X0)
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['48', '50'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('53', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.54  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('56', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.54            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v2_tex_2 @ X1 @ sk_B)
% 0.22/0.54          | ~ (v2_tex_2 @ X1 @ X0)
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['51', '54', '55', '56'])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | (v2_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('eq_res', [status(thm)], ['57'])).
% 0.22/0.54  thf('59', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.54      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.54  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('61', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.22/0.54  thf('62', plain,
% 0.22/0.54      ((~ (v2_tex_2 @ sk_C_1 @ sk_A) | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['47', '61'])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('64', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (v3_tex_2 @ X13 @ X14)
% 0.22/0.54          | (v2_tex_2 @ X13 @ X14)
% 0.22/0.54          | ~ (l1_pre_topc @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('65', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.22/0.54        | ~ (v3_tex_2 @ sk_C_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.54  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('67', plain, ((v3_tex_2 @ sk_C_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('68', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.22/0.54  thf('69', plain, ((v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['62', '68'])).
% 0.22/0.54  thf('70', plain,
% 0.22/0.54      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['46', '69'])).
% 0.22/0.54  thf('71', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('72', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (v3_tex_2 @ X13 @ X14)
% 0.22/0.54          | ~ (v2_tex_2 @ X15 @ X14)
% 0.22/0.54          | ~ (r1_tarski @ X13 @ X15)
% 0.22/0.54          | ((X13) = (X15))
% 0.22/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (l1_pre_topc @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('73', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((sk_C_1) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ sk_C_1 @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (v3_tex_2 @ sk_C_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.54  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('75', plain, ((v3_tex_2 @ sk_C_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('76', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((sk_C_1) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ sk_C_1 @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.22/0.54  thf('77', plain,
% 0.22/0.54      ((~ (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)
% 0.22/0.54        | ~ (r1_tarski @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.22/0.54        | ((sk_C_1) = (sk_C @ sk_C_1 @ sk_B)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['70', '76'])).
% 0.22/0.54  thf('78', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('79', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf('80', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (v2_tex_2 @ X13 @ X14)
% 0.22/0.54          | (r1_tarski @ X13 @ (sk_C @ X13 @ X14))
% 0.22/0.54          | (v3_tex_2 @ X13 @ X14)
% 0.22/0.54          | ~ (l1_pre_topc @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('81', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54          | (v3_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | (r1_tarski @ X0 @ (sk_C @ X0 @ sk_B))
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.54  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('83', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v3_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | (r1_tarski @ X0 @ (sk_C @ X0 @ sk_B))
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.54  thf('84', plain,
% 0.22/0.54      ((~ (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.22/0.54        | (r1_tarski @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.22/0.54        | (v3_tex_2 @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['78', '83'])).
% 0.22/0.54  thf('85', plain, (~ (v3_tex_2 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('86', plain,
% 0.22/0.54      (((r1_tarski @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.22/0.54        | ~ (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('clc', [status(thm)], ['84', '85'])).
% 0.22/0.54  thf('87', plain, ((v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['62', '68'])).
% 0.22/0.54  thf('88', plain, ((r1_tarski @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['86', '87'])).
% 0.22/0.54  thf('89', plain,
% 0.22/0.54      ((~ (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)
% 0.22/0.54        | ((sk_C_1) = (sk_C @ sk_C_1 @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['77', '88'])).
% 0.22/0.54  thf('90', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('91', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf('92', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (v2_tex_2 @ X13 @ X14)
% 0.22/0.54          | ((X13) != (sk_C @ X13 @ X14))
% 0.22/0.54          | (v3_tex_2 @ X13 @ X14)
% 0.22/0.54          | ~ (l1_pre_topc @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('93', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54          | (v3_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | ((X0) != (sk_C @ X0 @ sk_B))
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['91', '92'])).
% 0.22/0.54  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('95', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v3_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | ((X0) != (sk_C @ X0 @ sk_B))
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['93', '94'])).
% 0.22/0.54  thf('96', plain,
% 0.22/0.54      ((~ (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.22/0.54        | ((sk_C_1) != (sk_C @ sk_C_1 @ sk_B))
% 0.22/0.54        | (v3_tex_2 @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['90', '95'])).
% 0.22/0.54  thf('97', plain, (~ (v3_tex_2 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('98', plain,
% 0.22/0.54      ((((sk_C_1) != (sk_C @ sk_C_1 @ sk_B)) | ~ (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('clc', [status(thm)], ['96', '97'])).
% 0.22/0.54  thf('99', plain, ((v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['62', '68'])).
% 0.22/0.54  thf('100', plain, (((sk_C_1) != (sk_C @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['98', '99'])).
% 0.22/0.54  thf('101', plain, (~ (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['89', '100'])).
% 0.22/0.54  thf('102', plain,
% 0.22/0.54      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['46', '69'])).
% 0.22/0.54  thf('103', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf('104', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X19)
% 0.22/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.54          | ((g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19))
% 0.22/0.54              != (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.22/0.54          | ~ (v2_tex_2 @ X17 @ X19)
% 0.22/0.54          | (v2_tex_2 @ X17 @ X16)
% 0.22/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.54          | ~ (l1_pre_topc @ X16))),
% 0.22/0.54      inference('simplify', [status(thm)], ['49'])).
% 0.22/0.54  thf('105', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.22/0.54            != (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.54          | (v2_tex_2 @ X1 @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ X1 @ sk_B)
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.54          | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['103', '104'])).
% 0.22/0.54  thf('106', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.54  thf('107', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('109', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.22/0.54            != (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.54          | (v2_tex_2 @ X1 @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ X1 @ sk_B)
% 0.22/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.22/0.54  thf('110', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.54      inference('eq_res', [status(thm)], ['109'])).
% 0.22/0.54  thf('111', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['110'])).
% 0.22/0.54  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('113', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['111', '112'])).
% 0.22/0.54  thf('114', plain,
% 0.22/0.54      ((~ (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.22/0.54        | (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['102', '113'])).
% 0.22/0.54  thf('115', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('116', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '35'])).
% 0.22/0.54  thf('117', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (v2_tex_2 @ X13 @ X14)
% 0.22/0.54          | (v2_tex_2 @ (sk_C @ X13 @ X14) @ X14)
% 0.22/0.54          | (v3_tex_2 @ X13 @ X14)
% 0.22/0.54          | ~ (l1_pre_topc @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('118', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54          | (v3_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | (v2_tex_2 @ (sk_C @ X0 @ sk_B) @ sk_B)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['116', '117'])).
% 0.22/0.54  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('120', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v3_tex_2 @ X0 @ sk_B)
% 0.22/0.54          | (v2_tex_2 @ (sk_C @ X0 @ sk_B) @ sk_B)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['118', '119'])).
% 0.22/0.54  thf('121', plain,
% 0.22/0.54      ((~ (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.22/0.54        | (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.22/0.54        | (v3_tex_2 @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['115', '120'])).
% 0.22/0.54  thf('122', plain, (~ (v3_tex_2 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('123', plain,
% 0.22/0.54      (((v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.22/0.54        | ~ (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.22/0.54      inference('clc', [status(thm)], ['121', '122'])).
% 0.22/0.54  thf('124', plain, ((v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['62', '68'])).
% 0.22/0.54  thf('125', plain, ((v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['123', '124'])).
% 0.22/0.54  thf('126', plain, ((v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['114', '125'])).
% 0.22/0.54  thf('127', plain, ($false), inference('demod', [status(thm)], ['101', '126'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
