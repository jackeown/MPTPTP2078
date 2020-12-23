%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5sNGURTcbB

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:11 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 972 expanded)
%              Number of leaves         :   25 ( 273 expanded)
%              Depth                    :   20
%              Number of atoms          : 1270 (17400 expanded)
%              Number of equality atoms :   49 (1186 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('20',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('27',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( m1_subset_1 @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('46',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('50',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X19 )
       != ( sk_C @ X16 @ X17 ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( v2_tex_2 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','29'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ ( sk_D @ X18 @ X16 @ X17 ) )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
      = ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['44','45'])).

thf('67',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
    = ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ( ( sk_C @ sk_C_1 @ sk_B )
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['57','67'])).

thf('69',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('71',plain,(
    ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('73',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('74',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

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

thf('75',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ X13 @ X14 )
      | ( X13 != X11 )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('76',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ( v3_pre_topc @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','29'])).

thf('81',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( v3_pre_topc @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['44','45'])).

thf('89',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('91',plain,(
    ! [X15: $i] :
      ( ( m1_pre_topc @ X15 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('92',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['90','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ( m1_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['79','89','101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['71','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5sNGURTcbB
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 139 iterations in 0.082s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.35/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.35/0.54  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(t25_tex_2, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( l1_pre_topc @ B ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54               ( ![D:$i]:
% 0.35/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.35/0.54                   ( ( ( ( g1_pre_topc @
% 0.35/0.54                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.35/0.54                         ( g1_pre_topc @
% 0.35/0.54                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.35/0.54                       ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.35/0.54                     ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( l1_pre_topc @ A ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( l1_pre_topc @ B ) =>
% 0.35/0.54              ( ![C:$i]:
% 0.35/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54                  ( ![D:$i]:
% 0.35/0.54                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.35/0.54                      ( ( ( ( g1_pre_topc @
% 0.35/0.54                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.35/0.54                            ( g1_pre_topc @
% 0.35/0.54                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.35/0.54                          ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.35/0.54                        ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t25_tex_2])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain, (((sk_C_1) = (sk_D_1))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.54  thf(d5_tex_2, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( v2_tex_2 @ B @ A ) <=>
% 0.35/0.54             ( ![C:$i]:
% 0.35/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.35/0.54                      ( ![D:$i]:
% 0.35/0.54                        ( ( m1_subset_1 @
% 0.35/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.35/0.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.35/0.54                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | (m1_subset_1 @ (sk_C @ X16 @ X17) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | (v2_tex_2 @ X16 @ X17)
% 0.35/0.54          | ~ (l1_pre_topc @ X17))),
% 0.35/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.35/0.54        | (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.35/0.54        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.35/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.35/0.54        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.35/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.54  thf('7', plain, (~ (v2_tex_2 @ sk_D_1 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('8', plain, (((sk_C_1) = (sk_D_1))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('9', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.35/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.54      inference('clc', [status(thm)], ['6', '9'])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(dt_u1_pre_topc, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( m1_subset_1 @
% 0.35/0.54         ( u1_pre_topc @ A ) @ 
% 0.35/0.54         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.35/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.35/0.54          | ~ (l1_pre_topc @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.35/0.54  thf(free_g1_pre_topc, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.54       ( ![C:$i,D:$i]:
% 0.35/0.54         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.35/0.54           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.54         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.35/0.54          | ((X6) = (X4))
% 0.35/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.35/0.54      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X0)
% 0.35/0.54          | ((u1_pre_topc @ X0) = (X1))
% 0.35/0.54          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.35/0.54              != (g1_pre_topc @ X2 @ X1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.54            != (g1_pre_topc @ X1 @ X0))
% 0.35/0.54          | ((u1_pre_topc @ sk_B) = (X0))
% 0.35/0.54          | ~ (l1_pre_topc @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '14'])).
% 0.35/0.54  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.54            != (g1_pre_topc @ X1 @ X0))
% 0.35/0.54          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.35/0.54  thf('18', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.35/0.54      inference('eq_res', [status(thm)], ['17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.35/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.35/0.54          | ~ (l1_pre_topc @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.35/0.54         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.35/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.35/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.35/0.54  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.54         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.35/0.54          | ((X5) = (X3))
% 0.35/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.35/0.54      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((u1_struct_0 @ sk_B) = (X0))
% 0.35/0.54          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.35/0.54              != (g1_pre_topc @ X0 @ X1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('26', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.35/0.54      inference('eq_res', [status(thm)], ['17'])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((u1_struct_0 @ sk_B) = (X0))
% 0.35/0.54          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.54              != (g1_pre_topc @ X0 @ X1)))),
% 0.35/0.54      inference('demod', [status(thm)], ['24', '27'])).
% 0.35/0.54  thf('29', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('eq_res', [status(thm)], ['28'])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '29'])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (v2_tex_2 @ X16 @ X17)
% 0.35/0.54          | (m1_subset_1 @ (sk_D @ X18 @ X16 @ X17) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (r1_tarski @ X18 @ X16)
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (l1_pre_topc @ X17))),
% 0.35/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ sk_A)
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.35/0.54          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.54  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('35', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.35/0.54          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.35/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['30', '36'])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('39', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('eq_res', [status(thm)], ['28'])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | (r1_tarski @ (sk_C @ X16 @ X17) @ X16)
% 0.35/0.54          | (v2_tex_2 @ X16 @ X17)
% 0.35/0.54          | ~ (l1_pre_topc @ X17))),
% 0.35/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.35/0.54  thf('41', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.35/0.54          | (v2_tex_2 @ X0 @ sk_B)
% 0.35/0.54          | (r1_tarski @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.54  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | (v2_tex_2 @ X0 @ sk_B)
% 0.35/0.54          | (r1_tarski @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.35/0.54        | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['38', '43'])).
% 0.35/0.54  thf('45', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.35/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.35/0.54  thf('46', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.35/0.54      inference('clc', [status(thm)], ['44', '45'])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['37', '46'])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('49', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('eq_res', [status(thm)], ['28'])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (v3_pre_topc @ X19 @ X17)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X19)
% 0.35/0.54              != (sk_C @ X16 @ X17))
% 0.35/0.54          | (v2_tex_2 @ X16 @ X17)
% 0.35/0.54          | ~ (l1_pre_topc @ X17))),
% 0.35/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.35/0.54          | (v2_tex_2 @ X0 @ sk_B)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_B) @ X0 @ X1)
% 0.35/0.54              != (sk_C @ X0 @ sk_B))
% 0.35/0.54          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.35/0.54  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('53', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('eq_res', [status(thm)], ['28'])).
% 0.35/0.54  thf('54', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('eq_res', [status(thm)], ['28'])).
% 0.35/0.54  thf('55', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | (v2_tex_2 @ X0 @ sk_B)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X1)
% 0.35/0.54              != (sk_C @ X0 @ sk_B))
% 0.35/0.54          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.35/0.54  thf('56', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 0.35/0.54              != (sk_C @ sk_C_1 @ sk_B))
% 0.35/0.54          | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['48', '55'])).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.35/0.54        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.35/0.54            (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.35/0.54            != (sk_C @ sk_C_1 @ sk_B))
% 0.35/0.54        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.35/0.54             sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['47', '56'])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '29'])).
% 0.35/0.54  thf('59', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (v2_tex_2 @ X16 @ X17)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 0.35/0.54              (sk_D @ X18 @ X16 @ X17)) = (X18))
% 0.35/0.54          | ~ (r1_tarski @ X18 @ X16)
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (l1_pre_topc @ X17))),
% 0.35/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.35/0.54  thf('61', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ sk_A)
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.35/0.54              (sk_D @ X0 @ sk_C_1 @ sk_A)) = (X0))
% 0.35/0.54          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.35/0.54  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('63', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('64', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.35/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.35/0.54              (sk_D @ X0 @ sk_C_1 @ sk_A)) = (X0)))),
% 0.35/0.54      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.35/0.54  thf('65', plain,
% 0.35/0.54      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.35/0.54          (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.35/0.54          = (sk_C @ sk_C_1 @ sk_B))
% 0.35/0.54        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['58', '64'])).
% 0.35/0.54  thf('66', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.35/0.54      inference('clc', [status(thm)], ['44', '45'])).
% 0.35/0.54  thf('67', plain,
% 0.35/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.35/0.54         (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A))
% 0.35/0.54         = (sk_C @ sk_C_1 @ sk_B))),
% 0.35/0.54      inference('demod', [status(thm)], ['65', '66'])).
% 0.35/0.54  thf('68', plain,
% 0.35/0.54      (((v2_tex_2 @ sk_C_1 @ sk_B)
% 0.35/0.54        | ((sk_C @ sk_C_1 @ sk_B) != (sk_C @ sk_C_1 @ sk_B))
% 0.35/0.54        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.35/0.54             sk_B))),
% 0.35/0.54      inference('demod', [status(thm)], ['57', '67'])).
% 0.35/0.54  thf('69', plain,
% 0.35/0.54      ((~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)
% 0.35/0.54        | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.35/0.54      inference('simplify', [status(thm)], ['68'])).
% 0.35/0.54  thf('70', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.35/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.35/0.54  thf('71', plain,
% 0.35/0.54      (~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)),
% 0.35/0.54      inference('clc', [status(thm)], ['69', '70'])).
% 0.35/0.54  thf('72', plain,
% 0.35/0.54      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['37', '46'])).
% 0.35/0.54  thf('73', plain,
% 0.35/0.54      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['37', '46'])).
% 0.35/0.54  thf('74', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('eq_res', [status(thm)], ['28'])).
% 0.35/0.54  thf(t33_tops_2, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m1_pre_topc @ C @ A ) =>
% 0.35/0.54               ( ( v3_pre_topc @ B @ A ) =>
% 0.35/0.54                 ( ![D:$i]:
% 0.35/0.54                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.35/0.54                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('75', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.35/0.54          | ~ (v3_pre_topc @ X11 @ X12)
% 0.35/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.35/0.54          | (v3_pre_topc @ X13 @ X14)
% 0.35/0.54          | ((X13) != (X11))
% 0.35/0.54          | ~ (m1_pre_topc @ X14 @ X12)
% 0.35/0.54          | ~ (l1_pre_topc @ X12))),
% 0.35/0.54      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.35/0.54  thf('76', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X12)
% 0.35/0.54          | ~ (m1_pre_topc @ X14 @ X12)
% 0.35/0.54          | (v3_pre_topc @ X11 @ X14)
% 0.35/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.35/0.54          | ~ (v3_pre_topc @ X11 @ X12)
% 0.35/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['75'])).
% 0.35/0.54  thf('77', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.35/0.54          | ~ (v3_pre_topc @ X0 @ X1)
% 0.35/0.54          | (v3_pre_topc @ X0 @ sk_B)
% 0.35/0.54          | ~ (m1_pre_topc @ sk_B @ X1)
% 0.35/0.54          | ~ (l1_pre_topc @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['74', '76'])).
% 0.35/0.54  thf('78', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X0)
% 0.35/0.54          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.35/0.54          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.35/0.54             sk_B)
% 0.35/0.54          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.35/0.54               X0)
% 0.35/0.54          | ~ (m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['73', '77'])).
% 0.35/0.54  thf('79', plain,
% 0.35/0.54      ((~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)
% 0.35/0.54        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)
% 0.35/0.54        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['72', '78'])).
% 0.35/0.54  thf('80', plain,
% 0.35/0.54      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '29'])).
% 0.35/0.54  thf('81', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('82', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (v2_tex_2 @ X16 @ X17)
% 0.35/0.54          | (v3_pre_topc @ (sk_D @ X18 @ X16 @ X17) @ X17)
% 0.35/0.54          | ~ (r1_tarski @ X18 @ X16)
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | ~ (l1_pre_topc @ X17))),
% 0.35/0.54      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.35/0.54  thf('83', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ sk_A)
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.35/0.54          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A)
% 0.35/0.54          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['81', '82'])).
% 0.35/0.54  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('85', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('86', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.35/0.54          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.35/0.54  thf('87', plain,
% 0.35/0.54      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)
% 0.35/0.54        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['80', '86'])).
% 0.35/0.54  thf('88', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.35/0.54      inference('clc', [status(thm)], ['44', '45'])).
% 0.35/0.54  thf('89', plain,
% 0.35/0.54      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['87', '88'])).
% 0.35/0.54  thf('90', plain,
% 0.35/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.35/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t2_tsep_1, axiom,
% 0.35/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.35/0.54  thf('91', plain,
% 0.35/0.54      (![X15 : $i]: ((m1_pre_topc @ X15 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.35/0.54  thf(t65_pre_topc, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( l1_pre_topc @ B ) =>
% 0.35/0.54           ( ( m1_pre_topc @ A @ B ) <=>
% 0.35/0.54             ( m1_pre_topc @
% 0.35/0.54               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.35/0.54  thf('92', plain,
% 0.35/0.54      (![X9 : $i, X10 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X9)
% 0.35/0.54          | ~ (m1_pre_topc @ X10 @ X9)
% 0.35/0.54          | (m1_pre_topc @ X10 @ 
% 0.35/0.54             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.35/0.54          | ~ (l1_pre_topc @ X10))),
% 0.35/0.54      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.35/0.54  thf('93', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X0)
% 0.35/0.54          | ~ (l1_pre_topc @ X0)
% 0.35/0.54          | (m1_pre_topc @ X0 @ 
% 0.35/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.35/0.54          | ~ (l1_pre_topc @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['91', '92'])).
% 0.35/0.54  thf('94', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((m1_pre_topc @ X0 @ 
% 0.35/0.54           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.35/0.54          | ~ (l1_pre_topc @ X0))),
% 0.35/0.54      inference('simplify', [status(thm)], ['93'])).
% 0.35/0.54  thf('95', plain,
% 0.35/0.54      (((m1_pre_topc @ sk_B @ 
% 0.35/0.54         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.35/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.35/0.54      inference('sup+', [status(thm)], ['90', '94'])).
% 0.35/0.54  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('97', plain,
% 0.35/0.54      ((m1_pre_topc @ sk_B @ 
% 0.35/0.54        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['95', '96'])).
% 0.35/0.54  thf(t59_pre_topc, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_pre_topc @
% 0.35/0.54             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.35/0.54           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.35/0.54  thf('98', plain,
% 0.35/0.54      (![X7 : $i, X8 : $i]:
% 0.35/0.54         (~ (m1_pre_topc @ X7 @ 
% 0.35/0.54             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.35/0.54          | (m1_pre_topc @ X7 @ X8)
% 0.35/0.54          | ~ (l1_pre_topc @ X8))),
% 0.35/0.54      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.35/0.54  thf('99', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['97', '98'])).
% 0.35/0.54  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('101', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['99', '100'])).
% 0.35/0.54  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('103', plain,
% 0.35/0.54      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)),
% 0.35/0.54      inference('demod', [status(thm)], ['79', '89', '101', '102'])).
% 0.35/0.54  thf('104', plain, ($false), inference('demod', [status(thm)], ['71', '103'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
