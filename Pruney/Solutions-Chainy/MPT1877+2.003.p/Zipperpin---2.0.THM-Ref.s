%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I5cgd2AjMW

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:02 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :  263 (54851 expanded)
%              Number of leaves         :   25 (14850 expanded)
%              Depth                    :   35
%              Number of atoms          : 3000 (1001143 expanded)
%              Number of equality atoms :   86 (68384 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
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
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
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
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C_2 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('34',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_tex_2 @ X11 @ X12 )
      | ( v2_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_C_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_tex_2 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_tex_2 @ sk_C_2 @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','44'])).

thf('46',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(clc,[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('57',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X8 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X8 ) @ X7 @ X10 )
       != ( sk_C @ X7 @ X8 ) )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ X0 )
       != ( sk_C @ sk_C_2 @ sk_B ) )
      | ( v2_tex_2 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) )
     != ( sk_C @ sk_C_2 @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) )
     != ( sk_C @ sk_C_2 @ sk_B ) )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(clc,[status(thm)],['46','53'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('68',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('72',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( v3_pre_topc @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_2 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_tex_2 @ sk_C_2 @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_2 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','79'])).

thf('81',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( r2_hidden @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(clc,[status(thm)],['70','81'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(clc,[status(thm)],['46','53'])).

thf('84',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) )
     != ( sk_C @ sk_C_2 @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','92'])).

thf('94',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('95',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X8 ) @ X7 @ ( sk_D @ X9 @ X7 @ X8 ) )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ ( sk_D @ X0 @ sk_C_2 @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_tex_2 @ sk_C_2 @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ ( sk_D @ X0 @ sk_C_2 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) )
      = ( sk_C @ sk_C_2 @ sk_B ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,
    ( ( r1_tarski @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('103',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 @ ( sk_D @ ( sk_C @ sk_C_2 @ sk_B ) @ sk_C_2 @ sk_A ) )
      = ( sk_C @ sk_C_2 @ sk_B ) )
    | ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    v2_tex_2 @ sk_C_2 @ sk_B ),
    inference(clc,[status(thm)],['93','103'])).

thf('105',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['25','104'])).

thf('106',plain,(
    ~ ( v3_tex_2 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_C_2 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ~ ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_tex_2 @ X11 @ X12 )
      | ~ ( v2_tex_2 @ X13 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ( X11 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C_2 = X0 )
      | ~ ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v3_tex_2 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_C_2 = X0 )
      | ~ ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
    | ( sk_C_2
      = ( sk_C_1 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('118',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( X11
       != ( sk_C_1 @ X11 @ X12 ) )
      | ( v3_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v3_tex_2 @ sk_C_2 @ sk_B )
    | ( sk_C_2
     != ( sk_C_1 @ sk_C_2 @ sk_B ) )
    | ~ ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v3_tex_2 @ sk_C_2 @ sk_B )
    | ( sk_C_2
     != ( sk_C_1 @ sk_C_2 @ sk_B ) )
    | ~ ( v2_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('123',plain,
    ( ~ ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( sk_C_2
     != ( sk_C_1 @ sk_C_2 @ sk_B ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    v2_tex_2 @ sk_C_2 @ sk_B ),
    inference(clc,[status(thm)],['93','103'])).

thf('125',plain,(
    sk_C_2
 != ( sk_C_1 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['116','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('129',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( sk_C_1 @ X11 @ X12 ) )
      | ( v3_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ sk_B ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ sk_B ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
    | ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,(
    v2_tex_2 @ sk_C_2 @ sk_B ),
    inference(clc,[status(thm)],['93','103'])).

thf('135',plain,
    ( ( r1_tarski @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
    | ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('137',plain,(
    r1_tarski @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','137'])).

thf('139',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','108'])).

thf('140',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('141',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','108'])).

thf('145',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('146',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','108'])).

thf('150',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('151',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X8 ) @ X7 @ ( sk_D @ X9 @ X7 @ X8 ) )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( sk_D @ X1 @ X0 @ sk_B ) )
        = X1 )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('155',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D @ X1 @ X0 @ sk_B ) )
        = X1 )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( sk_D @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['149','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('160',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( v2_tex_2 @ ( sk_C_1 @ X11 @ X12 ) @ X12 )
      | ( v3_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( v2_tex_2 @ ( sk_C_1 @ X0 @ sk_B ) @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ X0 @ sk_B )
      | ( v2_tex_2 @ ( sk_C_1 @ X0 @ sk_B ) @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( v2_tex_2 @ sk_C_2 @ sk_B )
    | ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B )
    | ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['158','163'])).

thf('165',plain,(
    v2_tex_2 @ sk_C_2 @ sk_B ),
    inference(clc,[status(thm)],['93','103'])).

thf('166',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B )
    | ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v3_tex_2 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('168',plain,(
    v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( sk_D @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['157','168'])).

thf('170',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) )
      = ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','169'])).

thf('171',plain,(
    ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','137'])).

thf('172',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) )
      = ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) )
      = ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','172'])).

thf('174',plain,(
    ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','137'])).

thf('175',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) )
    = ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','108'])).

thf('177',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X8 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X8 ) @ X7 @ X10 )
       != ( sk_C @ X7 @ X8 ) )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ X0 )
       != ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ X0 )
       != ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
     != ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_A )
    | ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['175','180'])).

thf('182',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('183',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('184',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','108'])).

thf('185',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('186',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('190',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['184','191'])).

thf('193',plain,(
    v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['166','167'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['183','194'])).

thf('196',plain,(
    ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','137'])).

thf('197',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['182','197'])).

thf('199',plain,(
    ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','137'])).

thf('200',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('203',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('207',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['206','212'])).

thf('214',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('215',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('216',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','108'])).

thf('217',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('218',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( v3_pre_topc @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( v3_pre_topc @ ( sk_D @ X1 @ X0 @ sk_B ) @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( v3_pre_topc @ ( sk_D @ X1 @ X0 @ sk_B ) @ sk_B )
      | ~ ( v2_tex_2 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['216','222'])).

thf('224',plain,(
    v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['166','167'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['215','225'])).

thf('227',plain,(
    ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','137'])).

thf('228',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['214','228'])).

thf('230',plain,(
    ~ ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','137'])).

thf('231',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,(
    r2_hidden @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['213','231'])).

thf('233',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['205','232'])).

thf('234',plain,
    ( ( ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A )
     != ( sk_C @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) )
    | ( v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['181','200','233'])).

thf('235',plain,(
    v2_tex_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    $false ),
    inference(demod,[status(thm)],['138','235'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I5cgd2AjMW
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:07:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.12/1.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.12/1.34  % Solved by: fo/fo7.sh
% 1.12/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.12/1.34  % done 573 iterations in 0.850s
% 1.12/1.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.12/1.34  % SZS output start Refutation
% 1.12/1.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.12/1.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.12/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.12/1.34  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.12/1.34  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.12/1.34  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.12/1.34  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.12/1.34  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.12/1.34  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.12/1.34  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.12/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.12/1.34  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.12/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.12/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.12/1.34  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.12/1.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.12/1.34  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.12/1.34  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.12/1.34  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.12/1.34  thf(t45_tex_2, conjecture,
% 1.12/1.34    (![A:$i]:
% 1.12/1.34     ( ( l1_pre_topc @ A ) =>
% 1.12/1.34       ( ![B:$i]:
% 1.12/1.34         ( ( l1_pre_topc @ B ) =>
% 1.12/1.34           ( ![C:$i]:
% 1.12/1.34             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.12/1.34               ( ![D:$i]:
% 1.12/1.34                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.12/1.34                   ( ( ( ( g1_pre_topc @
% 1.12/1.34                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 1.12/1.34                         ( g1_pre_topc @
% 1.12/1.34                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 1.12/1.34                       ( ( C ) = ( D ) ) & ( v3_tex_2 @ C @ A ) ) =>
% 1.12/1.34                     ( v3_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 1.12/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.12/1.34    (~( ![A:$i]:
% 1.12/1.34        ( ( l1_pre_topc @ A ) =>
% 1.12/1.34          ( ![B:$i]:
% 1.12/1.34            ( ( l1_pre_topc @ B ) =>
% 1.12/1.34              ( ![C:$i]:
% 1.12/1.34                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.12/1.34                  ( ![D:$i]:
% 1.12/1.34                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.12/1.34                      ( ( ( ( g1_pre_topc @
% 1.12/1.34                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 1.12/1.34                            ( g1_pre_topc @
% 1.12/1.34                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 1.12/1.34                          ( ( C ) = ( D ) ) & ( v3_tex_2 @ C @ A ) ) =>
% 1.12/1.34                        ( v3_tex_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 1.12/1.34    inference('cnf.neg', [status(esa)], [t45_tex_2])).
% 1.12/1.34  thf('0', plain,
% 1.12/1.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('1', plain,
% 1.12/1.34      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.12/1.34         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf(dt_u1_pre_topc, axiom,
% 1.12/1.34    (![A:$i]:
% 1.12/1.34     ( ( l1_pre_topc @ A ) =>
% 1.12/1.34       ( m1_subset_1 @
% 1.12/1.34         ( u1_pre_topc @ A ) @ 
% 1.12/1.34         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.12/1.34  thf('2', plain,
% 1.12/1.34      (![X2 : $i]:
% 1.12/1.34         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 1.12/1.34           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 1.12/1.34          | ~ (l1_pre_topc @ X2))),
% 1.12/1.34      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.12/1.34  thf(free_g1_pre_topc, axiom,
% 1.12/1.34    (![A:$i,B:$i]:
% 1.12/1.34     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.12/1.34       ( ![C:$i,D:$i]:
% 1.12/1.34         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 1.12/1.34           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 1.12/1.34  thf('3', plain,
% 1.12/1.34      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.12/1.34         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 1.12/1.34          | ((X6) = (X4))
% 1.12/1.34          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 1.12/1.34      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.12/1.34  thf('4', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.34         (~ (l1_pre_topc @ X0)
% 1.12/1.34          | ((u1_pre_topc @ X0) = (X1))
% 1.12/1.34          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.12/1.34              != (g1_pre_topc @ X2 @ X1)))),
% 1.12/1.34      inference('sup-', [status(thm)], ['2', '3'])).
% 1.12/1.34  thf('5', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.12/1.34            != (g1_pre_topc @ X1 @ X0))
% 1.12/1.34          | ((u1_pre_topc @ sk_B) = (X0))
% 1.12/1.34          | ~ (l1_pre_topc @ sk_B))),
% 1.12/1.34      inference('sup-', [status(thm)], ['1', '4'])).
% 1.12/1.34  thf('6', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('7', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.12/1.34            != (g1_pre_topc @ X1 @ X0))
% 1.12/1.34          | ((u1_pre_topc @ sk_B) = (X0)))),
% 1.12/1.34      inference('demod', [status(thm)], ['5', '6'])).
% 1.12/1.34  thf('8', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 1.12/1.34      inference('eq_res', [status(thm)], ['7'])).
% 1.12/1.34  thf('9', plain,
% 1.12/1.34      (![X2 : $i]:
% 1.12/1.34         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 1.12/1.34           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 1.12/1.34          | ~ (l1_pre_topc @ X2))),
% 1.12/1.34      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.12/1.34  thf('10', plain,
% 1.12/1.34      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 1.12/1.34         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 1.12/1.34        | ~ (l1_pre_topc @ sk_B))),
% 1.12/1.34      inference('sup+', [status(thm)], ['8', '9'])).
% 1.12/1.34  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('12', plain,
% 1.12/1.34      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 1.12/1.34        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.12/1.34      inference('demod', [status(thm)], ['10', '11'])).
% 1.12/1.34  thf('13', plain,
% 1.12/1.34      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.12/1.34         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 1.12/1.34          | ((X5) = (X3))
% 1.12/1.34          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 1.12/1.34      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.12/1.34  thf('14', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         (((u1_struct_0 @ sk_B) = (X0))
% 1.12/1.34          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.12/1.34              != (g1_pre_topc @ X0 @ X1)))),
% 1.12/1.34      inference('sup-', [status(thm)], ['12', '13'])).
% 1.12/1.34  thf('15', plain,
% 1.12/1.34      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.12/1.34         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('16', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 1.12/1.34      inference('eq_res', [status(thm)], ['7'])).
% 1.12/1.34  thf('17', plain,
% 1.12/1.34      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.12/1.34         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.12/1.34      inference('demod', [status(thm)], ['15', '16'])).
% 1.12/1.34  thf('18', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         (((u1_struct_0 @ sk_B) = (X0))
% 1.12/1.34          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.12/1.34              != (g1_pre_topc @ X0 @ X1)))),
% 1.12/1.34      inference('demod', [status(thm)], ['14', '17'])).
% 1.12/1.34  thf('19', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.34      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.34  thf(d7_tex_2, axiom,
% 1.12/1.34    (![A:$i]:
% 1.12/1.34     ( ( l1_pre_topc @ A ) =>
% 1.12/1.34       ( ![B:$i]:
% 1.12/1.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.12/1.34           ( ( v3_tex_2 @ B @ A ) <=>
% 1.12/1.34             ( ( v2_tex_2 @ B @ A ) & 
% 1.12/1.34               ( ![C:$i]:
% 1.12/1.34                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.12/1.34                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.12/1.34                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 1.12/1.34  thf('20', plain,
% 1.12/1.34      (![X11 : $i, X12 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.12/1.34          | ~ (v2_tex_2 @ X11 @ X12)
% 1.12/1.34          | (m1_subset_1 @ (sk_C_1 @ X11 @ X12) @ 
% 1.12/1.34             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.12/1.34          | (v3_tex_2 @ X11 @ X12)
% 1.12/1.34          | ~ (l1_pre_topc @ X12))),
% 1.12/1.34      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.12/1.34  thf('21', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.34          | (v3_tex_2 @ X0 @ sk_B)
% 1.12/1.34          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_B) @ 
% 1.12/1.34             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.12/1.34          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.34      inference('sup-', [status(thm)], ['19', '20'])).
% 1.12/1.34  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('23', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.34      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.34  thf('24', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | (v3_tex_2 @ X0 @ sk_B)
% 1.12/1.34          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_B) @ 
% 1.12/1.34             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.34      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.12/1.34  thf('25', plain,
% 1.12/1.34      ((~ (v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | (m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34        | (v3_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.34      inference('sup-', [status(thm)], ['0', '24'])).
% 1.12/1.34  thf('26', plain,
% 1.12/1.34      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('27', plain, (((sk_C_2) = (sk_D_1))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('28', plain,
% 1.12/1.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 1.12/1.34      inference('demod', [status(thm)], ['26', '27'])).
% 1.12/1.34  thf(d5_tex_2, axiom,
% 1.12/1.34    (![A:$i]:
% 1.12/1.34     ( ( l1_pre_topc @ A ) =>
% 1.12/1.34       ( ![B:$i]:
% 1.12/1.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.12/1.34           ( ( v2_tex_2 @ B @ A ) <=>
% 1.12/1.34             ( ![C:$i]:
% 1.12/1.34               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.12/1.34                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.12/1.34                      ( ![D:$i]:
% 1.12/1.34                        ( ( m1_subset_1 @
% 1.12/1.34                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.12/1.34                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 1.12/1.34                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.12/1.34                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.12/1.34  thf('29', plain,
% 1.12/1.34      (![X7 : $i, X8 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | (m1_subset_1 @ (sk_C @ X7 @ X8) @ 
% 1.12/1.34             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | (v2_tex_2 @ X7 @ X8)
% 1.12/1.34          | ~ (l1_pre_topc @ X8))),
% 1.12/1.34      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.34  thf('30', plain,
% 1.12/1.34      ((~ (l1_pre_topc @ sk_B)
% 1.12/1.34        | (v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | (m1_subset_1 @ (sk_C @ sk_C_2 @ sk_B) @ 
% 1.12/1.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.12/1.34      inference('sup-', [status(thm)], ['28', '29'])).
% 1.12/1.34  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('32', plain,
% 1.12/1.34      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | (m1_subset_1 @ (sk_C @ sk_C_2 @ sk_B) @ 
% 1.12/1.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.12/1.34      inference('demod', [status(thm)], ['30', '31'])).
% 1.12/1.34  thf('33', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.34      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.34  thf('34', plain,
% 1.12/1.34      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | (m1_subset_1 @ (sk_C @ sk_C_2 @ sk_B) @ 
% 1.12/1.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.12/1.34  thf('35', plain,
% 1.12/1.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('36', plain,
% 1.12/1.34      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | ~ (v2_tex_2 @ X7 @ X8)
% 1.12/1.34          | (m1_subset_1 @ (sk_D @ X9 @ X7 @ X8) @ 
% 1.12/1.34             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | ~ (r1_tarski @ X9 @ X7)
% 1.12/1.34          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | ~ (l1_pre_topc @ X8))),
% 1.12/1.34      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.34  thf('37', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         (~ (l1_pre_topc @ sk_A)
% 1.12/1.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | ~ (r1_tarski @ X0 @ sk_C_2)
% 1.12/1.34          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_2 @ sk_A) @ 
% 1.12/1.34             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | ~ (v2_tex_2 @ sk_C_2 @ sk_A))),
% 1.12/1.34      inference('sup-', [status(thm)], ['35', '36'])).
% 1.12/1.34  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('39', plain,
% 1.12/1.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('40', plain,
% 1.12/1.34      (![X11 : $i, X12 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.12/1.34          | ~ (v3_tex_2 @ X11 @ X12)
% 1.12/1.34          | (v2_tex_2 @ X11 @ X12)
% 1.12/1.34          | ~ (l1_pre_topc @ X12))),
% 1.12/1.34      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.12/1.34  thf('41', plain,
% 1.12/1.34      ((~ (l1_pre_topc @ sk_A)
% 1.12/1.34        | (v2_tex_2 @ sk_C_2 @ sk_A)
% 1.12/1.34        | ~ (v3_tex_2 @ sk_C_2 @ sk_A))),
% 1.12/1.34      inference('sup-', [status(thm)], ['39', '40'])).
% 1.12/1.34  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('43', plain, ((v3_tex_2 @ sk_C_2 @ sk_A)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('44', plain, ((v2_tex_2 @ sk_C_2 @ sk_A)),
% 1.12/1.34      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.12/1.34  thf('45', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | ~ (r1_tarski @ X0 @ sk_C_2)
% 1.12/1.34          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_2 @ sk_A) @ 
% 1.12/1.34             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.34      inference('demod', [status(thm)], ['37', '38', '44'])).
% 1.12/1.34  thf('46', plain,
% 1.12/1.34      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | (m1_subset_1 @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34        | ~ (r1_tarski @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2))),
% 1.12/1.34      inference('sup-', [status(thm)], ['34', '45'])).
% 1.12/1.34  thf('47', plain,
% 1.12/1.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('48', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.34      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.34  thf('49', plain,
% 1.12/1.34      (![X7 : $i, X8 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | (r1_tarski @ (sk_C @ X7 @ X8) @ X7)
% 1.12/1.34          | (v2_tex_2 @ X7 @ X8)
% 1.12/1.34          | ~ (l1_pre_topc @ X8))),
% 1.12/1.34      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.34  thf('50', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.34          | (v2_tex_2 @ X0 @ sk_B)
% 1.12/1.34          | (r1_tarski @ (sk_C @ X0 @ sk_B) @ X0))),
% 1.12/1.34      inference('sup-', [status(thm)], ['48', '49'])).
% 1.12/1.34  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('52', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | (v2_tex_2 @ X0 @ sk_B)
% 1.12/1.34          | (r1_tarski @ (sk_C @ X0 @ sk_B) @ X0))),
% 1.12/1.34      inference('demod', [status(thm)], ['50', '51'])).
% 1.12/1.34  thf('53', plain,
% 1.12/1.34      (((r1_tarski @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2)
% 1.12/1.34        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.34      inference('sup-', [status(thm)], ['47', '52'])).
% 1.12/1.34  thf('54', plain,
% 1.12/1.34      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.34         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.34      inference('clc', [status(thm)], ['46', '53'])).
% 1.12/1.34  thf('55', plain,
% 1.12/1.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('56', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.34      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.34  thf('57', plain,
% 1.12/1.34      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | ~ (v3_pre_topc @ X10 @ X8)
% 1.12/1.34          | ((k9_subset_1 @ (u1_struct_0 @ X8) @ X7 @ X10) != (sk_C @ X7 @ X8))
% 1.12/1.34          | (v2_tex_2 @ X7 @ X8)
% 1.12/1.34          | ~ (l1_pre_topc @ X8))),
% 1.12/1.34      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.34  thf('58', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.34          | (v2_tex_2 @ X0 @ sk_B)
% 1.12/1.34          | ((k9_subset_1 @ (u1_struct_0 @ sk_B) @ X0 @ X1)
% 1.12/1.34              != (sk_C @ X0 @ sk_B))
% 1.12/1.34          | ~ (v3_pre_topc @ X1 @ sk_B)
% 1.12/1.34          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 1.12/1.34      inference('sup-', [status(thm)], ['56', '57'])).
% 1.12/1.34  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('60', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.34      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.34  thf('61', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.34      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.34  thf('62', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | (v2_tex_2 @ X0 @ sk_B)
% 1.12/1.34          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X1)
% 1.12/1.34              != (sk_C @ X0 @ sk_B))
% 1.12/1.34          | ~ (v3_pre_topc @ X1 @ sk_B)
% 1.12/1.34          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.34      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 1.12/1.34  thf('63', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34          | ~ (v3_pre_topc @ X0 @ sk_B)
% 1.12/1.34          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_2 @ X0)
% 1.12/1.34              != (sk_C @ sk_C_2 @ sk_B))
% 1.12/1.34          | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.34      inference('sup-', [status(thm)], ['55', '62'])).
% 1.12/1.34  thf('64', plain,
% 1.12/1.34      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | (v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_2 @ 
% 1.12/1.34            (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A))
% 1.12/1.34            != (sk_C @ sk_C_2 @ sk_B))
% 1.12/1.34        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.34             sk_B))),
% 1.12/1.34      inference('sup-', [status(thm)], ['54', '63'])).
% 1.12/1.34  thf('65', plain,
% 1.12/1.34      ((~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ sk_B)
% 1.12/1.34        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_2 @ 
% 1.12/1.34            (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A))
% 1.12/1.34            != (sk_C @ sk_C_2 @ sk_B))
% 1.12/1.34        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.34      inference('simplify', [status(thm)], ['64'])).
% 1.12/1.34  thf('66', plain,
% 1.12/1.34      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.34         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.34        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.34      inference('clc', [status(thm)], ['46', '53'])).
% 1.12/1.34  thf(d5_pre_topc, axiom,
% 1.12/1.34    (![A:$i]:
% 1.12/1.34     ( ( l1_pre_topc @ A ) =>
% 1.12/1.34       ( ![B:$i]:
% 1.12/1.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.12/1.34           ( ( v3_pre_topc @ B @ A ) <=>
% 1.12/1.34             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 1.12/1.34  thf('67', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.12/1.34          | ~ (v3_pre_topc @ X0 @ X1)
% 1.12/1.34          | (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 1.12/1.34          | ~ (l1_pre_topc @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [d5_pre_topc])).
% 1.12/1.34  thf('68', plain,
% 1.12/1.34      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | ~ (l1_pre_topc @ sk_A)
% 1.12/1.34        | (r2_hidden @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.34           (u1_pre_topc @ sk_A))
% 1.12/1.34        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.34             sk_A))),
% 1.12/1.34      inference('sup-', [status(thm)], ['66', '67'])).
% 1.12/1.34  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('70', plain,
% 1.12/1.34      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | (r2_hidden @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.34           (u1_pre_topc @ sk_A))
% 1.12/1.34        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.34             sk_A))),
% 1.12/1.34      inference('demod', [status(thm)], ['68', '69'])).
% 1.12/1.34  thf('71', plain,
% 1.12/1.34      (((r1_tarski @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2)
% 1.12/1.34        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.34      inference('sup-', [status(thm)], ['47', '52'])).
% 1.12/1.34  thf('72', plain,
% 1.12/1.34      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.34        | (m1_subset_1 @ (sk_C @ sk_C_2 @ sk_B) @ 
% 1.12/1.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.12/1.34  thf('73', plain,
% 1.12/1.34      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('74', plain,
% 1.12/1.34      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.12/1.34         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | ~ (v2_tex_2 @ X7 @ X8)
% 1.12/1.34          | (v3_pre_topc @ (sk_D @ X9 @ X7 @ X8) @ X8)
% 1.12/1.34          | ~ (r1_tarski @ X9 @ X7)
% 1.12/1.34          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.34          | ~ (l1_pre_topc @ X8))),
% 1.12/1.34      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.35  thf('75', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (l1_pre_topc @ sk_A)
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (r1_tarski @ X0 @ sk_C_2)
% 1.12/1.35          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_2 @ sk_A) @ sk_A)
% 1.12/1.35          | ~ (v2_tex_2 @ sk_C_2 @ sk_A))),
% 1.12/1.35      inference('sup-', [status(thm)], ['73', '74'])).
% 1.12/1.35  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('77', plain, ((v2_tex_2 @ sk_C_2 @ sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.12/1.35  thf('78', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (r1_tarski @ X0 @ sk_C_2)
% 1.12/1.35          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_2 @ sk_A) @ sk_A))),
% 1.12/1.35      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.12/1.35  thf('79', plain,
% 1.12/1.35      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ sk_A)
% 1.12/1.35        | ~ (r1_tarski @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2))),
% 1.12/1.35      inference('sup-', [status(thm)], ['72', '78'])).
% 1.12/1.35  thf('80', plain,
% 1.12/1.35      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ sk_A)
% 1.12/1.35        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['71', '79'])).
% 1.12/1.35  thf('81', plain,
% 1.12/1.35      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ sk_A)
% 1.12/1.35        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('simplify', [status(thm)], ['80'])).
% 1.12/1.35  thf('82', plain,
% 1.12/1.35      (((r2_hidden @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.35         (u1_pre_topc @ sk_A))
% 1.12/1.35        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('clc', [status(thm)], ['70', '81'])).
% 1.12/1.35  thf('83', plain,
% 1.12/1.35      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.35         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('clc', [status(thm)], ['46', '53'])).
% 1.12/1.35  thf('84', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('85', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.12/1.35          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 1.12/1.35          | (v3_pre_topc @ X0 @ X1)
% 1.12/1.35          | ~ (l1_pre_topc @ X1))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_pre_topc])).
% 1.12/1.35  thf('86', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.35          | (v3_pre_topc @ X0 @ sk_B)
% 1.12/1.35          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['84', '85'])).
% 1.12/1.35  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('88', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['7'])).
% 1.12/1.35  thf('89', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | (v3_pre_topc @ X0 @ sk_B)
% 1.12/1.35          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 1.12/1.35      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.12/1.35  thf('90', plain,
% 1.12/1.35      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | ~ (r2_hidden @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ 
% 1.12/1.35             (u1_pre_topc @ sk_A))
% 1.12/1.35        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['83', '89'])).
% 1.12/1.35  thf('91', plain,
% 1.12/1.35      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ sk_B)
% 1.12/1.35        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['82', '90'])).
% 1.12/1.35  thf('92', plain,
% 1.12/1.35      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A) @ sk_B)
% 1.12/1.35        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('simplify', [status(thm)], ['91'])).
% 1.12/1.35  thf('93', plain,
% 1.12/1.35      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_2 @ 
% 1.12/1.35            (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A))
% 1.12/1.35            != (sk_C @ sk_C_2 @ sk_B)))),
% 1.12/1.35      inference('clc', [status(thm)], ['65', '92'])).
% 1.12/1.35  thf('94', plain,
% 1.12/1.35      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | (m1_subset_1 @ (sk_C @ sk_C_2 @ sk_B) @ 
% 1.12/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('demod', [status(thm)], ['32', '33'])).
% 1.12/1.35  thf('95', plain,
% 1.12/1.35      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('96', plain,
% 1.12/1.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (v2_tex_2 @ X7 @ X8)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ X8) @ X7 @ (sk_D @ X9 @ X7 @ X8))
% 1.12/1.35              = (X9))
% 1.12/1.35          | ~ (r1_tarski @ X9 @ X7)
% 1.12/1.35          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (l1_pre_topc @ X8))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.35  thf('97', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (l1_pre_topc @ sk_A)
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (r1_tarski @ X0 @ sk_C_2)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_2 @ 
% 1.12/1.35              (sk_D @ X0 @ sk_C_2 @ sk_A)) = (X0))
% 1.12/1.35          | ~ (v2_tex_2 @ sk_C_2 @ sk_A))),
% 1.12/1.35      inference('sup-', [status(thm)], ['95', '96'])).
% 1.12/1.35  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('99', plain, ((v2_tex_2 @ sk_C_2 @ sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.12/1.35  thf('100', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (r1_tarski @ X0 @ sk_C_2)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_2 @ 
% 1.12/1.35              (sk_D @ X0 @ sk_C_2 @ sk_A)) = (X0)))),
% 1.12/1.35      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.12/1.35  thf('101', plain,
% 1.12/1.35      (((v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_2 @ 
% 1.12/1.35            (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A))
% 1.12/1.35            = (sk_C @ sk_C_2 @ sk_B))
% 1.12/1.35        | ~ (r1_tarski @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2))),
% 1.12/1.35      inference('sup-', [status(thm)], ['94', '100'])).
% 1.12/1.35  thf('102', plain,
% 1.12/1.35      (((r1_tarski @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2)
% 1.12/1.35        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['47', '52'])).
% 1.12/1.35  thf('103', plain,
% 1.12/1.35      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_2 @ 
% 1.12/1.35          (sk_D @ (sk_C @ sk_C_2 @ sk_B) @ sk_C_2 @ sk_A))
% 1.12/1.35          = (sk_C @ sk_C_2 @ sk_B))
% 1.12/1.35        | (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('clc', [status(thm)], ['101', '102'])).
% 1.12/1.35  thf('104', plain, ((v2_tex_2 @ sk_C_2 @ sk_B)),
% 1.12/1.35      inference('clc', [status(thm)], ['93', '103'])).
% 1.12/1.35  thf('105', plain,
% 1.12/1.35      (((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35        | (v3_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['25', '104'])).
% 1.12/1.35  thf('106', plain, (~ (v3_tex_2 @ sk_D_1 @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('107', plain, (((sk_C_2) = (sk_D_1))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('108', plain, (~ (v3_tex_2 @ sk_C_2 @ sk_B)),
% 1.12/1.35      inference('demod', [status(thm)], ['106', '107'])).
% 1.12/1.35  thf('109', plain,
% 1.12/1.35      ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['105', '108'])).
% 1.12/1.35  thf('110', plain,
% 1.12/1.35      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('111', plain,
% 1.12/1.35      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.12/1.35          | ~ (v3_tex_2 @ X11 @ X12)
% 1.12/1.35          | ~ (v2_tex_2 @ X13 @ X12)
% 1.12/1.35          | ~ (r1_tarski @ X11 @ X13)
% 1.12/1.35          | ((X11) = (X13))
% 1.12/1.35          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.12/1.35          | ~ (l1_pre_topc @ X12))),
% 1.12/1.35      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.12/1.35  thf('112', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (l1_pre_topc @ sk_A)
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ((sk_C_2) = (X0))
% 1.12/1.35          | ~ (r1_tarski @ sk_C_2 @ X0)
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_A)
% 1.12/1.35          | ~ (v3_tex_2 @ sk_C_2 @ sk_A))),
% 1.12/1.35      inference('sup-', [status(thm)], ['110', '111'])).
% 1.12/1.35  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('114', plain, ((v3_tex_2 @ sk_C_2 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('115', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ((sk_C_2) = (X0))
% 1.12/1.35          | ~ (r1_tarski @ sk_C_2 @ X0)
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_A))),
% 1.12/1.35      inference('demod', [status(thm)], ['112', '113', '114'])).
% 1.12/1.35  thf('116', plain,
% 1.12/1.35      ((~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | ~ (r1_tarski @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35        | ((sk_C_2) = (sk_C_1 @ sk_C_2 @ sk_B)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['109', '115'])).
% 1.12/1.35  thf('117', plain,
% 1.12/1.35      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 1.12/1.35      inference('demod', [status(thm)], ['26', '27'])).
% 1.12/1.35  thf('118', plain,
% 1.12/1.35      (![X11 : $i, X12 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.12/1.35          | ~ (v2_tex_2 @ X11 @ X12)
% 1.12/1.35          | ((X11) != (sk_C_1 @ X11 @ X12))
% 1.12/1.35          | (v3_tex_2 @ X11 @ X12)
% 1.12/1.35          | ~ (l1_pre_topc @ X12))),
% 1.12/1.35      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.12/1.35  thf('119', plain,
% 1.12/1.35      ((~ (l1_pre_topc @ sk_B)
% 1.12/1.35        | (v3_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | ((sk_C_2) != (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35        | ~ (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['117', '118'])).
% 1.12/1.35  thf('120', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('121', plain,
% 1.12/1.35      (((v3_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | ((sk_C_2) != (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35        | ~ (v2_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['119', '120'])).
% 1.12/1.35  thf('122', plain, (~ (v3_tex_2 @ sk_C_2 @ sk_B)),
% 1.12/1.35      inference('demod', [status(thm)], ['106', '107'])).
% 1.12/1.35  thf('123', plain,
% 1.12/1.35      ((~ (v2_tex_2 @ sk_C_2 @ sk_B) | ((sk_C_2) != (sk_C_1 @ sk_C_2 @ sk_B)))),
% 1.12/1.35      inference('clc', [status(thm)], ['121', '122'])).
% 1.12/1.35  thf('124', plain, ((v2_tex_2 @ sk_C_2 @ sk_B)),
% 1.12/1.35      inference('clc', [status(thm)], ['93', '103'])).
% 1.12/1.35  thf('125', plain, (((sk_C_2) != (sk_C_1 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['123', '124'])).
% 1.12/1.35  thf('126', plain,
% 1.12/1.35      ((~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | ~ (r1_tarski @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B)))),
% 1.12/1.35      inference('simplify_reflect-', [status(thm)], ['116', '125'])).
% 1.12/1.35  thf('127', plain,
% 1.12/1.35      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('128', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('129', plain,
% 1.12/1.35      (![X11 : $i, X12 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.12/1.35          | ~ (v2_tex_2 @ X11 @ X12)
% 1.12/1.35          | (r1_tarski @ X11 @ (sk_C_1 @ X11 @ X12))
% 1.12/1.35          | (v3_tex_2 @ X11 @ X12)
% 1.12/1.35          | ~ (l1_pre_topc @ X12))),
% 1.12/1.35      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.12/1.35  thf('130', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.35          | (v3_tex_2 @ X0 @ sk_B)
% 1.12/1.35          | (r1_tarski @ X0 @ (sk_C_1 @ X0 @ sk_B))
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['128', '129'])).
% 1.12/1.35  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('132', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | (v3_tex_2 @ X0 @ sk_B)
% 1.12/1.35          | (r1_tarski @ X0 @ (sk_C_1 @ X0 @ sk_B))
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['130', '131'])).
% 1.12/1.35  thf('133', plain,
% 1.12/1.35      ((~ (v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | (r1_tarski @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35        | (v3_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['127', '132'])).
% 1.12/1.35  thf('134', plain, ((v2_tex_2 @ sk_C_2 @ sk_B)),
% 1.12/1.35      inference('clc', [status(thm)], ['93', '103'])).
% 1.12/1.35  thf('135', plain,
% 1.12/1.35      (((r1_tarski @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35        | (v3_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['133', '134'])).
% 1.12/1.35  thf('136', plain, (~ (v3_tex_2 @ sk_C_2 @ sk_B)),
% 1.12/1.35      inference('demod', [status(thm)], ['106', '107'])).
% 1.12/1.35  thf('137', plain, ((r1_tarski @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('clc', [status(thm)], ['135', '136'])).
% 1.12/1.35  thf('138', plain, (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['126', '137'])).
% 1.12/1.35  thf('139', plain,
% 1.12/1.35      ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['105', '108'])).
% 1.12/1.35  thf('140', plain,
% 1.12/1.35      (![X7 : $i, X8 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | (m1_subset_1 @ (sk_C @ X7 @ X8) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | (v2_tex_2 @ X7 @ X8)
% 1.12/1.35          | ~ (l1_pre_topc @ X8))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.35  thf('141', plain,
% 1.12/1.35      ((~ (l1_pre_topc @ sk_A)
% 1.12/1.35        | (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('sup-', [status(thm)], ['139', '140'])).
% 1.12/1.35  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('143', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('demod', [status(thm)], ['141', '142'])).
% 1.12/1.35  thf('144', plain,
% 1.12/1.35      ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['105', '108'])).
% 1.12/1.35  thf('145', plain,
% 1.12/1.35      (![X7 : $i, X8 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | (r1_tarski @ (sk_C @ X7 @ X8) @ X7)
% 1.12/1.35          | (v2_tex_2 @ X7 @ X8)
% 1.12/1.35          | ~ (l1_pre_topc @ X8))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.35  thf('146', plain,
% 1.12/1.35      ((~ (l1_pre_topc @ sk_A)
% 1.12/1.35        | (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (r1_tarski @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35           (sk_C_1 @ sk_C_2 @ sk_B)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['144', '145'])).
% 1.12/1.35  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('148', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (r1_tarski @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35           (sk_C_1 @ sk_C_2 @ sk_B)))),
% 1.12/1.35      inference('demod', [status(thm)], ['146', '147'])).
% 1.12/1.35  thf('149', plain,
% 1.12/1.35      ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['105', '108'])).
% 1.12/1.35  thf('150', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('151', plain,
% 1.12/1.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (v2_tex_2 @ X7 @ X8)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ X8) @ X7 @ (sk_D @ X9 @ X7 @ X8))
% 1.12/1.35              = (X9))
% 1.12/1.35          | ~ (r1_tarski @ X9 @ X7)
% 1.12/1.35          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (l1_pre_topc @ X8))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.35  thf('152', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.12/1.35          | ~ (r1_tarski @ X1 @ X0)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ sk_B) @ X0 @ (sk_D @ X1 @ X0 @ sk_B))
% 1.12/1.35              = (X1))
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['150', '151'])).
% 1.12/1.35  thf('153', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('154', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('155', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('156', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (r1_tarski @ X1 @ X0)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ (sk_D @ X1 @ X0 @ sk_B))
% 1.12/1.35              = (X1))
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 1.12/1.35  thf('157', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35              (sk_D @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)) = (X0))
% 1.12/1.35          | ~ (r1_tarski @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('sup-', [status(thm)], ['149', '156'])).
% 1.12/1.35  thf('158', plain,
% 1.12/1.35      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('159', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('160', plain,
% 1.12/1.35      (![X11 : $i, X12 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.12/1.35          | ~ (v2_tex_2 @ X11 @ X12)
% 1.12/1.35          | (v2_tex_2 @ (sk_C_1 @ X11 @ X12) @ X12)
% 1.12/1.35          | (v3_tex_2 @ X11 @ X12)
% 1.12/1.35          | ~ (l1_pre_topc @ X12))),
% 1.12/1.35      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.12/1.35  thf('161', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.35          | (v3_tex_2 @ X0 @ sk_B)
% 1.12/1.35          | (v2_tex_2 @ (sk_C_1 @ X0 @ sk_B) @ sk_B)
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['159', '160'])).
% 1.12/1.35  thf('162', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('163', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | (v3_tex_2 @ X0 @ sk_B)
% 1.12/1.35          | (v2_tex_2 @ (sk_C_1 @ X0 @ sk_B) @ sk_B)
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['161', '162'])).
% 1.12/1.35  thf('164', plain,
% 1.12/1.35      ((~ (v2_tex_2 @ sk_C_2 @ sk_B)
% 1.12/1.35        | (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)
% 1.12/1.35        | (v3_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['158', '163'])).
% 1.12/1.35  thf('165', plain, ((v2_tex_2 @ sk_C_2 @ sk_B)),
% 1.12/1.35      inference('clc', [status(thm)], ['93', '103'])).
% 1.12/1.35  thf('166', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)
% 1.12/1.35        | (v3_tex_2 @ sk_C_2 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['164', '165'])).
% 1.12/1.35  thf('167', plain, (~ (v3_tex_2 @ sk_C_2 @ sk_B)),
% 1.12/1.35      inference('demod', [status(thm)], ['106', '107'])).
% 1.12/1.35  thf('168', plain, ((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)),
% 1.12/1.35      inference('clc', [status(thm)], ['166', '167'])).
% 1.12/1.35  thf('169', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35            (sk_D @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)) = (X0))
% 1.12/1.35          | ~ (r1_tarski @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('demod', [status(thm)], ['157', '168'])).
% 1.12/1.35  thf('170', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | ~ (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35            (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35             (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B))
% 1.12/1.35            = (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['148', '169'])).
% 1.12/1.35  thf('171', plain, (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['126', '137'])).
% 1.12/1.35  thf('172', plain,
% 1.12/1.35      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35          (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35           (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B))
% 1.12/1.35          = (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A))
% 1.12/1.35        | ~ (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('clc', [status(thm)], ['170', '171'])).
% 1.12/1.35  thf('173', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35            (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35             (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B))
% 1.12/1.35            = (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['143', '172'])).
% 1.12/1.35  thf('174', plain, (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['126', '137'])).
% 1.12/1.35  thf('175', plain,
% 1.12/1.35      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35         (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35          (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B))
% 1.12/1.35         = (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A))),
% 1.12/1.35      inference('clc', [status(thm)], ['173', '174'])).
% 1.12/1.35  thf('176', plain,
% 1.12/1.35      ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['105', '108'])).
% 1.12/1.35  thf('177', plain,
% 1.12/1.35      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (v3_pre_topc @ X10 @ X8)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ X8) @ X7 @ X10) != (sk_C @ X7 @ X8))
% 1.12/1.35          | (v2_tex_2 @ X7 @ X8)
% 1.12/1.35          | ~ (l1_pre_topc @ X8))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.35  thf('178', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (l1_pre_topc @ sk_A)
% 1.12/1.35          | (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35              X0) != (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A))
% 1.12/1.35          | ~ (v3_pre_topc @ X0 @ sk_A)
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('sup-', [status(thm)], ['176', '177'])).
% 1.12/1.35  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('180', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35              X0) != (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A))
% 1.12/1.35          | ~ (v3_pre_topc @ X0 @ sk_A)
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('demod', [status(thm)], ['178', '179'])).
% 1.12/1.35  thf('181', plain,
% 1.12/1.35      ((((sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35          != (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A))
% 1.12/1.35        | ~ (m1_subset_1 @ 
% 1.12/1.35             (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35              (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35        | ~ (v3_pre_topc @ 
% 1.12/1.35             (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35              (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35             sk_A)
% 1.12/1.35        | (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A))),
% 1.12/1.35      inference('sup-', [status(thm)], ['175', '180'])).
% 1.12/1.35  thf('182', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('demod', [status(thm)], ['141', '142'])).
% 1.12/1.35  thf('183', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (r1_tarski @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35           (sk_C_1 @ sk_C_2 @ sk_B)))),
% 1.12/1.35      inference('demod', [status(thm)], ['146', '147'])).
% 1.12/1.35  thf('184', plain,
% 1.12/1.35      ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['105', '108'])).
% 1.12/1.35  thf('185', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('186', plain,
% 1.12/1.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (v2_tex_2 @ X7 @ X8)
% 1.12/1.35          | (m1_subset_1 @ (sk_D @ X9 @ X7 @ X8) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (r1_tarski @ X9 @ X7)
% 1.12/1.35          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (l1_pre_topc @ X8))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.35  thf('187', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.12/1.35          | ~ (r1_tarski @ X1 @ X0)
% 1.12/1.35          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ sk_B) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['185', '186'])).
% 1.12/1.35  thf('188', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('189', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('190', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('191', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (r1_tarski @ X1 @ X0)
% 1.12/1.35          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ sk_B) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 1.12/1.35  thf('192', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)
% 1.12/1.35          | (m1_subset_1 @ (sk_D @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (r1_tarski @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('sup-', [status(thm)], ['184', '191'])).
% 1.12/1.35  thf('193', plain, ((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)),
% 1.12/1.35      inference('clc', [status(thm)], ['166', '167'])).
% 1.12/1.35  thf('194', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((m1_subset_1 @ (sk_D @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (r1_tarski @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('demod', [status(thm)], ['192', '193'])).
% 1.12/1.35  thf('195', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | ~ (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35        | (m1_subset_1 @ 
% 1.12/1.35           (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35            (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('sup-', [status(thm)], ['183', '194'])).
% 1.12/1.35  thf('196', plain, (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['126', '137'])).
% 1.12/1.35  thf('197', plain,
% 1.12/1.35      (((m1_subset_1 @ 
% 1.12/1.35         (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35          (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35        | ~ (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('clc', [status(thm)], ['195', '196'])).
% 1.12/1.35  thf('198', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (m1_subset_1 @ 
% 1.12/1.35           (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35            (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('sup-', [status(thm)], ['182', '197'])).
% 1.12/1.35  thf('199', plain, (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['126', '137'])).
% 1.12/1.35  thf('200', plain,
% 1.12/1.35      ((m1_subset_1 @ 
% 1.12/1.35        (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35         (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['198', '199'])).
% 1.12/1.35  thf('201', plain,
% 1.12/1.35      ((m1_subset_1 @ 
% 1.12/1.35        (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35         (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['198', '199'])).
% 1.12/1.35  thf('202', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.12/1.35          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 1.12/1.35          | (v3_pre_topc @ X0 @ X1)
% 1.12/1.35          | ~ (l1_pre_topc @ X1))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_pre_topc])).
% 1.12/1.35  thf('203', plain,
% 1.12/1.35      ((~ (l1_pre_topc @ sk_A)
% 1.12/1.35        | (v3_pre_topc @ 
% 1.12/1.35           (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35            (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35           sk_A)
% 1.12/1.35        | ~ (r2_hidden @ 
% 1.12/1.35             (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35              (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35             (u1_pre_topc @ sk_A)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['201', '202'])).
% 1.12/1.35  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('205', plain,
% 1.12/1.35      (((v3_pre_topc @ 
% 1.12/1.35         (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35          (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35         sk_A)
% 1.12/1.35        | ~ (r2_hidden @ 
% 1.12/1.35             (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35              (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35             (u1_pre_topc @ sk_A)))),
% 1.12/1.35      inference('demod', [status(thm)], ['203', '204'])).
% 1.12/1.35  thf('206', plain,
% 1.12/1.35      ((m1_subset_1 @ 
% 1.12/1.35        (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35         (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['198', '199'])).
% 1.12/1.35  thf('207', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('208', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.12/1.35          | ~ (v3_pre_topc @ X0 @ X1)
% 1.12/1.35          | (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 1.12/1.35          | ~ (l1_pre_topc @ X1))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_pre_topc])).
% 1.12/1.35  thf('209', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.35          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B))
% 1.12/1.35          | ~ (v3_pre_topc @ X0 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['207', '208'])).
% 1.12/1.35  thf('210', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('211', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['7'])).
% 1.12/1.35  thf('212', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 1.12/1.35          | ~ (v3_pre_topc @ X0 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['209', '210', '211'])).
% 1.12/1.35  thf('213', plain,
% 1.12/1.35      ((~ (v3_pre_topc @ 
% 1.12/1.35           (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35            (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35           sk_B)
% 1.12/1.35        | (r2_hidden @ 
% 1.12/1.35           (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35            (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35           (u1_pre_topc @ sk_A)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['206', '212'])).
% 1.12/1.35  thf('214', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('demod', [status(thm)], ['141', '142'])).
% 1.12/1.35  thf('215', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (r1_tarski @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35           (sk_C_1 @ sk_C_2 @ sk_B)))),
% 1.12/1.35      inference('demod', [status(thm)], ['146', '147'])).
% 1.12/1.35  thf('216', plain,
% 1.12/1.35      ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B) @ 
% 1.12/1.35        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('clc', [status(thm)], ['105', '108'])).
% 1.12/1.35  thf('217', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('218', plain,
% 1.12/1.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (v2_tex_2 @ X7 @ X8)
% 1.12/1.35          | (v3_pre_topc @ (sk_D @ X9 @ X7 @ X8) @ X8)
% 1.12/1.35          | ~ (r1_tarski @ X9 @ X7)
% 1.12/1.35          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.12/1.35          | ~ (l1_pre_topc @ X8))),
% 1.12/1.35      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.12/1.35  thf('219', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 1.12/1.35          | ~ (r1_tarski @ X1 @ X0)
% 1.12/1.35          | (v3_pre_topc @ (sk_D @ X1 @ X0 @ sk_B) @ sk_B)
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['217', '218'])).
% 1.12/1.35  thf('220', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('221', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('eq_res', [status(thm)], ['18'])).
% 1.12/1.35  thf('222', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35          | ~ (r1_tarski @ X1 @ X0)
% 1.12/1.35          | (v3_pre_topc @ (sk_D @ X1 @ X0 @ sk_B) @ sk_B)
% 1.12/1.35          | ~ (v2_tex_2 @ X0 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)], ['219', '220', '221'])).
% 1.12/1.35  thf('223', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)
% 1.12/1.35          | (v3_pre_topc @ (sk_D @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ sk_B)
% 1.12/1.35          | ~ (r1_tarski @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('sup-', [status(thm)], ['216', '222'])).
% 1.12/1.35  thf('224', plain, ((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)),
% 1.12/1.35      inference('clc', [status(thm)], ['166', '167'])).
% 1.12/1.35  thf('225', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v3_pre_topc @ (sk_D @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ sk_B)
% 1.12/1.35          | ~ (r1_tarski @ X0 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('demod', [status(thm)], ['223', '224'])).
% 1.12/1.35  thf('226', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | ~ (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.12/1.35        | (v3_pre_topc @ 
% 1.12/1.35           (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35            (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35           sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['215', '225'])).
% 1.12/1.35  thf('227', plain, (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['126', '137'])).
% 1.12/1.35  thf('228', plain,
% 1.12/1.35      (((v3_pre_topc @ 
% 1.12/1.35         (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35          (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35         sk_B)
% 1.12/1.35        | ~ (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.12/1.35      inference('clc', [status(thm)], ['226', '227'])).
% 1.12/1.35  thf('229', plain,
% 1.12/1.35      (((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35        | (v3_pre_topc @ 
% 1.12/1.35           (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35            (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35           sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['214', '228'])).
% 1.12/1.35  thf('230', plain, (~ (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['126', '137'])).
% 1.12/1.35  thf('231', plain,
% 1.12/1.35      ((v3_pre_topc @ 
% 1.12/1.35        (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35         (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35        sk_B)),
% 1.12/1.35      inference('clc', [status(thm)], ['229', '230'])).
% 1.12/1.35  thf('232', plain,
% 1.12/1.35      ((r2_hidden @ 
% 1.12/1.35        (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35         (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35        (u1_pre_topc @ sk_A))),
% 1.12/1.35      inference('demod', [status(thm)], ['213', '231'])).
% 1.12/1.35  thf('233', plain,
% 1.12/1.35      ((v3_pre_topc @ 
% 1.12/1.35        (sk_D @ (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A) @ 
% 1.12/1.35         (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) @ 
% 1.12/1.35        sk_A)),
% 1.12/1.35      inference('demod', [status(thm)], ['205', '232'])).
% 1.12/1.35  thf('234', plain,
% 1.12/1.35      ((((sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)
% 1.12/1.35          != (sk_C @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A))
% 1.12/1.35        | (v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A))),
% 1.12/1.35      inference('demod', [status(thm)], ['181', '200', '233'])).
% 1.12/1.35  thf('235', plain, ((v2_tex_2 @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_A)),
% 1.12/1.35      inference('simplify', [status(thm)], ['234'])).
% 1.12/1.35  thf('236', plain, ($false), inference('demod', [status(thm)], ['138', '235'])).
% 1.12/1.35  
% 1.12/1.35  % SZS output end Refutation
% 1.12/1.35  
% 1.12/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
