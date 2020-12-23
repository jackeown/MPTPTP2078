%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j86zjewA0y

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 495 expanded)
%              Number of leaves         :   22 ( 146 expanded)
%              Depth                    :   15
%              Number of atoms          : 1076 (9336 expanded)
%              Number of equality atoms :   46 ( 543 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v2_tex_2 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
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

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X8 ) @ X7 @ ( sk_D @ X9 @ X7 @ X8 ) )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
      = ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('33',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
    = ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','18'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['31','32'])).

thf('44',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('47',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X8 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X8 ) @ X7 @ X10 )
       != ( sk_C @ X7 @ X8 ) )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('51',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( v2_tex_2 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf('55',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('62',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['55','68'])).

thf('70',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','18'])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( v3_pre_topc @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A )
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
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['31','32'])).

thf('83',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r2_hidden @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','83'])).

thf('85',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['69','84'])).

thf('86',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
     != ( sk_C @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','85'])).

thf('87',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('88',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
 != ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j86zjewA0y
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 95 iterations in 0.084s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.54  thf(t25_tex_2, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( l1_pre_topc @ B ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54               ( ![D:$i]:
% 0.20/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.54                   ( ( ( ( g1_pre_topc @
% 0.20/0.54                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.54                         ( g1_pre_topc @
% 0.20/0.54                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.54                       ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.20/0.54                     ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( l1_pre_topc @ A ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( l1_pre_topc @ B ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54                  ( ![D:$i]:
% 0.20/0.54                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.54                      ( ( ( ( g1_pre_topc @
% 0.20/0.54                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.54                            ( g1_pre_topc @
% 0.20/0.54                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.54                          ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.20/0.54                        ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t25_tex_2])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain, (((sk_C_1) = (sk_D_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf(d5_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.54             ( ![C:$i]:
% 0.20/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.20/0.54                      ( ![D:$i]:
% 0.20/0.54                        ( ( m1_subset_1 @
% 0.20/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.20/0.54                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | (m1_subset_1 @ (sk_C @ X7 @ X8) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | (v2_tex_2 @ X7 @ X8)
% 0.20/0.54          | ~ (l1_pre_topc @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.54        | (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.20/0.54        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.20/0.54        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain, (~ (v2_tex_2 @ sk_D_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('8', plain, (((sk_C_1) = (sk_D_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('9', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['6', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_u1_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( m1_subset_1 @
% 0.20/0.54         ( u1_pre_topc @ A ) @ 
% 0.20/0.54         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X2 : $i]:
% 0.20/0.54         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.20/0.54          | ~ (l1_pre_topc @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.54  thf(free_g1_pre_topc, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.54       ( ![C:$i,D:$i]:
% 0.20/0.54         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.20/0.54           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.20/0.54          | ((X5) = (X3))
% 0.20/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.54      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X0)
% 0.20/0.54          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.54          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.54              != (g1_pre_topc @ X1 @ X2)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.54          | ((u1_struct_0 @ sk_B) = (X1))
% 0.20/0.54          | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.54  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.54          | ((u1_struct_0 @ sk_B) = (X1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('eq_res', [status(thm)], ['17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['10', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (v2_tex_2 @ X7 @ X8)
% 0.20/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X8) @ X7 @ (sk_D @ X9 @ X7 @ X8))
% 0.20/0.54              = (X9))
% 0.20/0.54          | ~ (r1_tarski @ X9 @ X7)
% 0.20/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (l1_pre_topc @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.20/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.54              (sk_D @ X0 @ sk_C_1 @ sk_A)) = (X0))
% 0.20/0.54          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('24', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.20/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.54              (sk_D @ X0 @ sk_C_1 @ sk_A)) = (X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.54          (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.20/0.54          = (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.54        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | (r1_tarski @ (sk_C @ X7 @ X8) @ X7)
% 0.20/0.54          | (v2_tex_2 @ X7 @ X8)
% 0.20/0.54          | ~ (l1_pre_topc @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.54        | (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.20/0.54        | (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.20/0.54        | (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('33', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.20/0.54      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.54         (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.20/0.54         = (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['26', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['10', '18'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (v2_tex_2 @ X7 @ X8)
% 0.20/0.54          | (m1_subset_1 @ (sk_D @ X9 @ X7 @ X8) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (r1_tarski @ X9 @ X7)
% 0.20/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (l1_pre_topc @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.20/0.54          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.55  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('40', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.20/0.55          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['35', '41'])).
% 0.20/0.55  thf('43', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.20/0.55      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('46', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['17'])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ~ (v3_pre_topc @ X10 @ X8)
% 0.20/0.55          | ((k9_subset_1 @ (u1_struct_0 @ X8) @ X7 @ X10) != (sk_C @ X7 @ X8))
% 0.20/0.55          | (v2_tex_2 @ X7 @ X8)
% 0.20/0.55          | ~ (l1_pre_topc @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.55          | (v2_tex_2 @ X0 @ sk_B)
% 0.20/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_B) @ X0 @ X1)
% 0.20/0.55              != (sk_C @ X0 @ sk_B))
% 0.20/0.55          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.55  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('50', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['17'])).
% 0.20/0.55  thf('51', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['17'])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | (v2_tex_2 @ X0 @ sk_B)
% 0.20/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X1)
% 0.20/0.55              != (sk_C @ X0 @ sk_B))
% 0.20/0.55          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.20/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 0.20/0.55              != (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.55          | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '52'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.20/0.55        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.55            (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.20/0.55            != (sk_C @ sk_C_1 @ sk_B))
% 0.20/0.55        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.20/0.55             sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.55  thf('56', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['17'])).
% 0.20/0.55  thf(d5_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.55             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.20/0.55          | (v3_pre_topc @ X0 @ X1)
% 0.20/0.55          | ~ (l1_pre_topc @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.55          | (v3_pre_topc @ X0 @ sk_B)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.55  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X2 : $i]:
% 0.20/0.55         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.20/0.55           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.20/0.55          | ~ (l1_pre_topc @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.20/0.55          | ((X6) = (X4))
% 0.20/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.55      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X0)
% 0.20/0.55          | ((u1_pre_topc @ X0) = (X1))
% 0.20/0.55          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.55              != (g1_pre_topc @ X2 @ X1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.55            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.55          | ((u1_pre_topc @ sk_B) = (X0))
% 0.20/0.55          | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['60', '63'])).
% 0.20/0.55  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.55            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.55          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.55  thf('67', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | (v3_pre_topc @ X0 @ sk_B)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['58', '59', '67'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      ((~ (r2_hidden @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.20/0.55           (u1_pre_topc @ sk_A))
% 0.20/0.55        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['55', '68'])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.55          | ~ (v3_pre_topc @ X0 @ X1)
% 0.20/0.55          | (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.20/0.55          | ~ (l1_pre_topc @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | (r2_hidden @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.20/0.55           (u1_pre_topc @ sk_A))
% 0.20/0.55        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.20/0.55             sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.55  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['10', '18'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ~ (v2_tex_2 @ X7 @ X8)
% 0.20/0.55          | (v3_pre_topc @ (sk_D @ X9 @ X7 @ X8) @ X8)
% 0.20/0.55          | ~ (r1_tarski @ X9 @ X7)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.55          | ~ (l1_pre_topc @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.20/0.55          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A)
% 0.20/0.55          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.55  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('79', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.20/0.55          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)
% 0.20/0.55        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['74', '80'])).
% 0.20/0.55  thf('82', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.20/0.55      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['81', '82'])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      ((r2_hidden @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.20/0.55        (u1_pre_topc @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['72', '73', '83'])).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['69', '84'])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.20/0.55        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.55            (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.20/0.55            != (sk_C @ sk_C_1 @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['54', '85'])).
% 0.20/0.55  thf('87', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.20/0.55         (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.20/0.55         != (sk_C @ sk_C_1 @ sk_B))),
% 0.20/0.55      inference('clc', [status(thm)], ['86', '87'])).
% 0.20/0.55  thf('89', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['34', '88'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
