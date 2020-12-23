%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XzyMAwoFkx

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:22 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 216 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  711 (2600 expanded)
%              Number of equality atoms :   22 (  91 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(t33_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( v4_pre_topc @ D @ A )
                              & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                                = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tex_2])).

thf('0',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X41: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X39 @ X38 )
      | ( r1_tarski @ X39 @ X37 )
      | ( X38
       != ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ X39 @ X37 )
      | ~ ( r2_hidden @ X39 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['8','11'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X42: $i,X43: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X42 ) @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tex_2,axiom,(
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
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v2_tex_2 @ X48 @ X49 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( sk_D_1 @ X50 @ X48 @ X49 ) )
        = X50 )
      | ~ ( r1_tarski @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X42: $i,X43: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X42 ) @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('30',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X41: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('34',plain,(
    r2_hidden @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ X39 @ X37 )
      | ~ ( r2_hidden @ X39 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v2_tex_2 @ X48 @ X49 )
      | ( m1_subset_1 @ ( sk_D_1 @ X50 @ X48 @ X49 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( r1_tarski @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('47',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X52: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X52 )
       != ( k1_tarski @ sk_C_2 ) )
      | ~ ( v4_pre_topc @ X52 @ sk_A )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v4_pre_topc @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v2_tex_2 @ X48 @ X49 )
      | ( v4_pre_topc @ ( sk_D_1 @ X50 @ X48 @ X49 ) @ X49 )
      | ~ ( r1_tarski @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( v4_pre_topc @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('59',plain,(
    v4_pre_topc @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XzyMAwoFkx
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.69  % Solved by: fo/fo7.sh
% 0.50/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.69  % done 347 iterations in 0.257s
% 0.50/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.69  % SZS output start Refutation
% 0.50/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.69  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.50/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.69  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.50/0.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.50/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.69  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.50/0.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.50/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.50/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.69  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.50/0.69  thf(t33_tex_2, conjecture,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ( l1_pre_topc @ A ) =>
% 0.50/0.69       ( ![B:$i]:
% 0.50/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69           ( ( v2_tex_2 @ B @ A ) =>
% 0.50/0.69             ( ![C:$i]:
% 0.50/0.69               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.69                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.50/0.69                      ( ![D:$i]:
% 0.50/0.69                        ( ( m1_subset_1 @
% 0.50/0.69                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.50/0.69                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.50/0.69                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.69    (~( ![A:$i]:
% 0.50/0.69        ( ( l1_pre_topc @ A ) =>
% 0.50/0.69          ( ![B:$i]:
% 0.50/0.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69              ( ( v2_tex_2 @ B @ A ) =>
% 0.50/0.69                ( ![C:$i]:
% 0.50/0.69                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.69                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.50/0.69                         ( ![D:$i]:
% 0.50/0.69                           ( ( m1_subset_1 @
% 0.50/0.69                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.50/0.69                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.50/0.69                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.50/0.69    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.50/0.69  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('1', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(t2_subset, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ A @ B ) =>
% 0.50/0.69       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.50/0.69  thf('2', plain,
% 0.50/0.69      (![X46 : $i, X47 : $i]:
% 0.50/0.69         ((r2_hidden @ X46 @ X47)
% 0.50/0.69          | (v1_xboole_0 @ X47)
% 0.50/0.69          | ~ (m1_subset_1 @ X46 @ X47))),
% 0.50/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.50/0.69  thf('3', plain,
% 0.50/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.69  thf(fc1_subset_1, axiom,
% 0.50/0.69    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.50/0.69  thf('4', plain, (![X41 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X41))),
% 0.50/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.50/0.69  thf('5', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('clc', [status(thm)], ['3', '4'])).
% 0.50/0.69  thf(d1_zfmisc_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.50/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.50/0.69  thf('6', plain,
% 0.50/0.69      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X39 @ X38)
% 0.50/0.69          | (r1_tarski @ X39 @ X37)
% 0.50/0.69          | ((X38) != (k1_zfmisc_1 @ X37)))),
% 0.50/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.50/0.69  thf('7', plain,
% 0.50/0.69      (![X37 : $i, X39 : $i]:
% 0.50/0.69         ((r1_tarski @ X39 @ X37) | ~ (r2_hidden @ X39 @ (k1_zfmisc_1 @ X37)))),
% 0.50/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.50/0.69  thf('8', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['5', '7'])).
% 0.50/0.69  thf(t28_xboole_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.69  thf('9', plain,
% 0.50/0.69      (![X6 : $i, X7 : $i]:
% 0.50/0.69         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.50/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.69  thf(t12_setfam_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.50/0.69  thf('10', plain,
% 0.50/0.69      (![X44 : $i, X45 : $i]:
% 0.50/0.69         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.50/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.50/0.69  thf('11', plain,
% 0.50/0.69      (![X6 : $i, X7 : $i]:
% 0.50/0.69         (((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (X6))
% 0.50/0.69          | ~ (r1_tarski @ X6 @ X7))),
% 0.50/0.69      inference('demod', [status(thm)], ['9', '10'])).
% 0.50/0.69  thf('12', plain,
% 0.50/0.69      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['8', '11'])).
% 0.50/0.69  thf(d4_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.50/0.69       ( ![D:$i]:
% 0.50/0.69         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.69           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.50/0.69  thf('13', plain,
% 0.50/0.69      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X4 @ X3)
% 0.50/0.69          | (r2_hidden @ X4 @ X2)
% 0.50/0.69          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.50/0.69      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.50/0.69  thf('14', plain,
% 0.50/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.50/0.69         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.50/0.69      inference('simplify', [status(thm)], ['13'])).
% 0.50/0.69  thf('15', plain,
% 0.50/0.69      (![X44 : $i, X45 : $i]:
% 0.50/0.69         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.50/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.50/0.69  thf('16', plain,
% 0.50/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.50/0.69         ((r2_hidden @ X4 @ X2)
% 0.50/0.69          | ~ (r2_hidden @ X4 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 0.50/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.50/0.69  thf('17', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['12', '16'])).
% 0.50/0.69  thf('18', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['0', '17'])).
% 0.50/0.69  thf(t63_subset_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r2_hidden @ A @ B ) =>
% 0.50/0.69       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.50/0.69  thf('19', plain,
% 0.50/0.69      (![X42 : $i, X43 : $i]:
% 0.50/0.69         ((m1_subset_1 @ (k1_tarski @ X42) @ (k1_zfmisc_1 @ X43))
% 0.50/0.69          | ~ (r2_hidden @ X42 @ X43))),
% 0.50/0.69      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.50/0.69  thf('20', plain,
% 0.50/0.69      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.50/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.69  thf('21', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(d6_tex_2, axiom,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ( l1_pre_topc @ A ) =>
% 0.50/0.69       ( ![B:$i]:
% 0.50/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69           ( ( v2_tex_2 @ B @ A ) <=>
% 0.50/0.69             ( ![C:$i]:
% 0.50/0.69               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.50/0.69                      ( ![D:$i]:
% 0.50/0.69                        ( ( m1_subset_1 @
% 0.50/0.69                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.50/0.69                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.50/0.69                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.69  thf('22', plain,
% 0.50/0.69      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.50/0.69          | ~ (v2_tex_2 @ X48 @ X49)
% 0.50/0.69          | ((k9_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 0.50/0.69              (sk_D_1 @ X50 @ X48 @ X49)) = (X50))
% 0.50/0.69          | ~ (r1_tarski @ X50 @ X48)
% 0.50/0.69          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.50/0.69          | ~ (l1_pre_topc @ X49))),
% 0.50/0.69      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.50/0.69  thf('23', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (~ (l1_pre_topc @ sk_A)
% 0.50/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | ~ (r1_tarski @ X0 @ sk_B)
% 0.50/0.69          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.69              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (X0))
% 0.50/0.69          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.69  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('25', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('26', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | ~ (r1_tarski @ X0 @ sk_B)
% 0.50/0.69          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.69              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.50/0.69      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.50/0.69  thf('27', plain,
% 0.50/0.69      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.69          (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))
% 0.50/0.69        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['20', '26'])).
% 0.50/0.69  thf('28', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('29', plain,
% 0.50/0.69      (![X42 : $i, X43 : $i]:
% 0.50/0.69         ((m1_subset_1 @ (k1_tarski @ X42) @ (k1_zfmisc_1 @ X43))
% 0.50/0.69          | ~ (r2_hidden @ X42 @ X43))),
% 0.50/0.69      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.50/0.69  thf('30', plain,
% 0.50/0.69      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.69  thf('31', plain,
% 0.50/0.69      (![X46 : $i, X47 : $i]:
% 0.50/0.69         ((r2_hidden @ X46 @ X47)
% 0.50/0.69          | (v1_xboole_0 @ X47)
% 0.50/0.69          | ~ (m1_subset_1 @ X46 @ X47))),
% 0.50/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.50/0.69  thf('32', plain,
% 0.50/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.50/0.69        | (r2_hidden @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.69  thf('33', plain, (![X41 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X41))),
% 0.50/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.50/0.69  thf('34', plain, ((r2_hidden @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.50/0.69      inference('clc', [status(thm)], ['32', '33'])).
% 0.50/0.69  thf('35', plain,
% 0.50/0.69      (![X37 : $i, X39 : $i]:
% 0.50/0.69         ((r1_tarski @ X39 @ X37) | ~ (r2_hidden @ X39 @ (k1_zfmisc_1 @ X37)))),
% 0.50/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.50/0.69  thf('36', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.50/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.50/0.69  thf('37', plain,
% 0.50/0.69      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.69         (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))),
% 0.50/0.69      inference('demod', [status(thm)], ['27', '36'])).
% 0.50/0.69  thf('38', plain,
% 0.50/0.69      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.50/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.69  thf('39', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('40', plain,
% 0.50/0.69      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.50/0.69          | ~ (v2_tex_2 @ X48 @ X49)
% 0.50/0.69          | (m1_subset_1 @ (sk_D_1 @ X50 @ X48 @ X49) @ 
% 0.50/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.50/0.69          | ~ (r1_tarski @ X50 @ X48)
% 0.50/0.69          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.50/0.69          | ~ (l1_pre_topc @ X49))),
% 0.50/0.69      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.50/0.69  thf('41', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (~ (l1_pre_topc @ sk_A)
% 0.50/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | ~ (r1_tarski @ X0 @ sk_B)
% 0.50/0.69          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.50/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['39', '40'])).
% 0.50/0.69  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('43', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('44', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | ~ (r1_tarski @ X0 @ sk_B)
% 0.50/0.69          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.50/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.69      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.50/0.69  thf('45', plain,
% 0.50/0.69      (((m1_subset_1 @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.50/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['38', '44'])).
% 0.50/0.69  thf('46', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.50/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.50/0.69  thf('47', plain,
% 0.50/0.69      ((m1_subset_1 @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.50/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('demod', [status(thm)], ['45', '46'])).
% 0.50/0.69  thf('48', plain,
% 0.50/0.69      (![X52 : $i]:
% 0.50/0.69         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X52)
% 0.50/0.69            != (k1_tarski @ sk_C_2))
% 0.50/0.69          | ~ (v4_pre_topc @ X52 @ sk_A)
% 0.50/0.69          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('49', plain,
% 0.50/0.69      ((~ (v4_pre_topc @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.50/0.69        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.69            (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A))
% 0.50/0.69            != (k1_tarski @ sk_C_2)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.69  thf('50', plain,
% 0.50/0.69      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.50/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.69  thf('51', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('52', plain,
% 0.50/0.69      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.50/0.69          | ~ (v2_tex_2 @ X48 @ X49)
% 0.50/0.69          | (v4_pre_topc @ (sk_D_1 @ X50 @ X48 @ X49) @ X49)
% 0.50/0.69          | ~ (r1_tarski @ X50 @ X48)
% 0.50/0.69          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.50/0.69          | ~ (l1_pre_topc @ X49))),
% 0.50/0.69      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.50/0.69  thf('53', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (~ (l1_pre_topc @ sk_A)
% 0.50/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | ~ (r1_tarski @ X0 @ sk_B)
% 0.50/0.69          | (v4_pre_topc @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.50/0.69          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.50/0.69  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('55', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('56', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | ~ (r1_tarski @ X0 @ sk_B)
% 0.50/0.69          | (v4_pre_topc @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.50/0.69      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.50/0.69  thf('57', plain,
% 0.50/0.69      (((v4_pre_topc @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.50/0.69        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['50', '56'])).
% 0.50/0.69  thf('58', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.50/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.50/0.69  thf('59', plain,
% 0.50/0.69      ((v4_pre_topc @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)),
% 0.50/0.69      inference('demod', [status(thm)], ['57', '58'])).
% 0.50/0.69  thf('60', plain,
% 0.50/0.69      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.69         (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_2))),
% 0.50/0.69      inference('demod', [status(thm)], ['49', '59'])).
% 0.50/0.69  thf('61', plain, ($false),
% 0.50/0.69      inference('simplify_reflect-', [status(thm)], ['37', '60'])).
% 0.50/0.69  
% 0.50/0.69  % SZS output end Refutation
% 0.50/0.69  
% 0.50/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
