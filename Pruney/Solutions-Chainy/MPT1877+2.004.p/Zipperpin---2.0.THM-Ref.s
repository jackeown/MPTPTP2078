%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CAtCldsHs1

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 (1186 expanded)
%              Number of leaves         :   19 ( 327 expanded)
%              Depth                    :   22
%              Number of atoms          : 1220 (21219 expanded)
%              Number of equality atoms :   59 (1535 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_pre_topc @ X3 @ X4 )
       != ( g1_pre_topc @ X1 @ X2 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('10',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_pre_topc @ X3 @ X4 )
       != ( g1_pre_topc @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('17',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

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

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_tex_2 @ X5 @ X6 )
      | ( m1_subset_1 @ ( sk_C @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v3_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    ~ ( v3_tex_2 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

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

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v2_tex_2 @ X9 @ X8 )
      | ( X10 != X9 )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_tex_2])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( v2_tex_2 @ X9 @ X11 )
      | ( v2_tex_2 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_tex_2 @ X1 @ sk_B )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X1 @ sk_B )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_tex_2 @ X5 @ X6 )
      | ( v2_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    v2_tex_2 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['43','49'])).

thf('51',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_tex_2 @ X5 @ X6 )
      | ~ ( v2_tex_2 @ X7 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( X5 = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C_1 = X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C_1 = X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ~ ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ( sk_C_1
      = ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_tex_2 @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( sk_C @ X5 @ X6 ) )
      | ( v3_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ X0 @ ( sk_C @ X0 @ sk_B ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ X0 @ ( sk_C @ X0 @ sk_B ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( r1_tarski @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    ~ ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('67',plain,
    ( ( r1_tarski @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    v2_tex_2 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['43','49'])).

thf('69',plain,(
    r1_tarski @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A )
    | ( sk_C_1
      = ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_tex_2 @ X5 @ X6 )
      | ( X5
       != ( sk_C @ X5 @ X6 ) )
      | ( v3_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v3_tex_2 @ sk_C_1 @ sk_B )
    | ( sk_C_1
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v3_tex_2 @ sk_C_1 @ sk_B )
    | ( sk_C_1
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('79',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( sk_C_1
     != ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    v2_tex_2 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['43','49'])).

thf('81',plain,(
    sk_C_1
 != ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['70','81'])).

thf('83',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','50'])).

thf('84',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('85',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( v2_tex_2 @ X9 @ X11 )
      | ( v2_tex_2 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v2_tex_2 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v2_tex_2 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('98',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_tex_2 @ X5 @ X6 )
      | ( v2_tex_2 @ ( sk_C @ X5 @ X6 ) @ X6 )
      | ( v3_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( v2_tex_2 @ ( sk_C @ X0 @ sk_B ) @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( v2_tex_2 @ ( sk_C @ X0 @ sk_B ) @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    ~ ( v3_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('104',plain,
    ( ( v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    v2_tex_2 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['43','49'])).

thf('106',plain,(
    v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    v2_tex_2 @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['95','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['82','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CAtCldsHs1
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:36:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 70 iterations in 0.040s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.50  thf(t45_tex_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( l1_pre_topc @ B ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.50                   ( ( ( ( g1_pre_topc @
% 0.21/0.50                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.50                         ( g1_pre_topc @
% 0.21/0.50                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.50                       ( ( C ) = ( D ) ) & ( v3_tex_2 @ C @ A ) ) =>
% 0.21/0.50                     ( v3_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( l1_pre_topc @ A ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( l1_pre_topc @ B ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                  ( ![D:$i]:
% 0.21/0.50                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.50                      ( ( ( ( g1_pre_topc @
% 0.21/0.50                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.50                            ( g1_pre_topc @
% 0.21/0.50                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.50                          ( ( C ) = ( D ) ) & ( v3_tex_2 @ C @ A ) ) =>
% 0.21/0.50                        ( v3_tex_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t45_tex_2])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_u1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( m1_subset_1 @
% 0.21/0.50         ( u1_pre_topc @ A ) @ 
% 0.21/0.50         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.50  thf(free_g1_pre_topc, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ![C:$i,D:$i]:
% 0.21/0.50         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.50           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (((g1_pre_topc @ X3 @ X4) != (g1_pre_topc @ X1 @ X2))
% 0.21/0.50          | ((X4) = (X2))
% 0.21/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.21/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X0)
% 0.21/0.50          | ((u1_pre_topc @ X0) = (X1))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.50              != (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.50            != (g1_pre_topc @ X1 @ X0))
% 0.21/0.50          | ((u1_pre_topc @ sk_B) = (X0))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf('6', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.50            != (g1_pre_topc @ X1 @ X0))
% 0.21/0.50          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.21/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (((g1_pre_topc @ X3 @ X4) != (g1_pre_topc @ X1 @ X2))
% 0.21/0.50          | ((X3) = (X1))
% 0.21/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.21/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((u1_struct_0 @ sk_B) = (X0))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.21/0.50              != (g1_pre_topc @ X0 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['7'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((u1_struct_0 @ sk_B) = (X0))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.50              != (g1_pre_topc @ X0 @ X1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '17'])).
% 0.21/0.50  thf('19', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.21/0.50  thf(d7_tex_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.50             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.50               ( ![C:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.50                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.50          | ~ (v2_tex_2 @ X5 @ X6)
% 0.21/0.50          | (m1_subset_1 @ (sk_C @ X5 @ X6) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.50          | (v3_tex_2 @ X5 @ X6)
% 0.21/0.50          | ~ (l1_pre_topc @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | (v3_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | (v3_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((~ (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.21/0.50        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | (v3_tex_2 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '24'])).
% 0.21/0.50  thf('26', plain, (~ (v3_tex_2 @ sk_D @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain, (((sk_C_1) = (sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain, (~ (v3_tex_2 @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['25', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.21/0.50  thf(t25_tex_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( l1_pre_topc @ B ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.50                   ( ( ( ( g1_pre_topc @
% 0.21/0.50                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.50                         ( g1_pre_topc @
% 0.21/0.50                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.50                       ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.21/0.50                     ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | (v2_tex_2 @ X9 @ X8)
% 0.21/0.50          | ((X10) != (X9))
% 0.21/0.50          | ~ (v2_tex_2 @ X10 @ X11)
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))
% 0.21/0.50              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.21/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ~ (l1_pre_topc @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t25_tex_2])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X11)
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))
% 0.21/0.50              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.21/0.50          | ~ (v2_tex_2 @ X9 @ X11)
% 0.21/0.50          | (v2_tex_2 @ X9 @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | ~ (l1_pre_topc @ X8))),
% 0.21/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.50            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_B)))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.50          | (v2_tex_2 @ X1 @ sk_B)
% 0.21/0.50          | ~ (v2_tex_2 @ X1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '33'])).
% 0.21/0.50  thf('35', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['7'])).
% 0.21/0.50  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.50            != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | (v2_tex_2 @ X1 @ sk_B)
% 0.21/0.50          | ~ (v2_tex_2 @ X1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.50          | (v2_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.50  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((~ (v2_tex_2 @ sk_C_1 @ sk_A) | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.50          | ~ (v3_tex_2 @ X5 @ X6)
% 0.21/0.50          | (v2_tex_2 @ X5 @ X6)
% 0.21/0.50          | ~ (l1_pre_topc @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.50        | ~ (v3_tex_2 @ sk_C_1 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain, ((v3_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.50  thf('50', plain, ((v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.50          | ~ (v3_tex_2 @ X5 @ X6)
% 0.21/0.50          | ~ (v2_tex_2 @ X7 @ X6)
% 0.21/0.50          | ~ (r1_tarski @ X5 @ X7)
% 0.21/0.50          | ((X5) = (X7))
% 0.21/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.50          | ~ (l1_pre_topc @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ((sk_C_1) = (X0))
% 0.21/0.50          | ~ (r1_tarski @ sk_C_1 @ X0)
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.50          | ~ (v3_tex_2 @ sk_C_1 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain, ((v3_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ((sk_C_1) = (X0))
% 0.21/0.50          | ~ (r1_tarski @ sk_C_1 @ X0)
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      ((~ (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)
% 0.21/0.50        | ~ (r1_tarski @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.50        | ((sk_C_1) = (sk_C @ sk_C_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['51', '57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.50          | ~ (v2_tex_2 @ X5 @ X6)
% 0.21/0.50          | (r1_tarski @ X5 @ (sk_C @ X5 @ X6))
% 0.21/0.50          | (v3_tex_2 @ X5 @ X6)
% 0.21/0.50          | ~ (l1_pre_topc @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | (v3_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ X0 @ (sk_C @ X0 @ sk_B))
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.50  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | (v3_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ X0 @ (sk_C @ X0 @ sk_B))
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      ((~ (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.21/0.50        | (r1_tarski @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.50        | (v3_tex_2 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['59', '64'])).
% 0.21/0.50  thf('66', plain, (~ (v3_tex_2 @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (((r1_tarski @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.50  thf('68', plain, ((v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '49'])).
% 0.21/0.50  thf('69', plain, ((r1_tarski @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      ((~ (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)
% 0.21/0.50        | ((sk_C_1) = (sk_C @ sk_C_1 @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['58', '69'])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('72', plain, (((sk_C_1) = (sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.50          | ~ (v2_tex_2 @ X5 @ X6)
% 0.21/0.50          | ((X5) != (sk_C @ X5 @ X6))
% 0.21/0.50          | (v3_tex_2 @ X5 @ X6)
% 0.21/0.50          | ~ (l1_pre_topc @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('75', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.50        | (v3_tex_2 @ sk_C_1 @ sk_B)
% 0.21/0.50        | ((sk_C_1) != (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.50  thf('76', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      (((v3_tex_2 @ sk_C_1 @ sk_B)
% 0.21/0.50        | ((sk_C_1) != (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.50  thf('78', plain, (~ (v3_tex_2 @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      ((~ (v2_tex_2 @ sk_C_1 @ sk_B) | ((sk_C_1) != (sk_C @ sk_C_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['77', '78'])).
% 0.21/0.50  thf('80', plain, ((v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '49'])).
% 0.21/0.50  thf('81', plain, (((sk_C_1) != (sk_C @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.50  thf('82', plain, (~ (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['70', '81'])).
% 0.21/0.50  thf('83', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '50'])).
% 0.21/0.50  thf('84', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X11)
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))
% 0.21/0.50              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.21/0.50          | ~ (v2_tex_2 @ X9 @ X11)
% 0.21/0.50          | (v2_tex_2 @ X9 @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | ~ (l1_pre_topc @ X8))),
% 0.21/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.21/0.50            != (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | (v2_tex_2 @ X1 @ X0)
% 0.21/0.50          | ~ (v2_tex_2 @ X1 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.50  thf('87', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['7'])).
% 0.21/0.50  thf('88', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.21/0.50  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.50            != (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | (v2_tex_2 @ X1 @ X0)
% 0.21/0.50          | ~ (v2_tex_2 @ X1 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.21/0.50  thf('91', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['90'])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['91'])).
% 0.21/0.50  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('94', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_tex_2 @ X0 @ sk_A)
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['92', '93'])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      ((~ (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.21/0.50        | (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['83', '94'])).
% 0.21/0.50  thf('96', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('97', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.21/0.50  thf('98', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.50          | ~ (v2_tex_2 @ X5 @ X6)
% 0.21/0.50          | (v2_tex_2 @ (sk_C @ X5 @ X6) @ X6)
% 0.21/0.50          | (v3_tex_2 @ X5 @ X6)
% 0.21/0.50          | ~ (l1_pre_topc @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('99', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | (v3_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | (v2_tex_2 @ (sk_C @ X0 @ sk_B) @ sk_B)
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.50  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('101', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | (v3_tex_2 @ X0 @ sk_B)
% 0.21/0.50          | (v2_tex_2 @ (sk_C @ X0 @ sk_B) @ sk_B)
% 0.21/0.50          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['99', '100'])).
% 0.21/0.50  thf('102', plain,
% 0.21/0.50      ((~ (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.21/0.50        | (v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.21/0.50        | (v3_tex_2 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['96', '101'])).
% 0.21/0.50  thf('103', plain, (~ (v3_tex_2 @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('104', plain,
% 0.21/0.50      (((v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.21/0.50        | ~ (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['102', '103'])).
% 0.21/0.50  thf('105', plain, ((v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '49'])).
% 0.21/0.50  thf('106', plain, ((v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['104', '105'])).
% 0.21/0.50  thf('107', plain, ((v2_tex_2 @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['95', '106'])).
% 0.21/0.50  thf('108', plain, ($false), inference('demod', [status(thm)], ['82', '107'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
