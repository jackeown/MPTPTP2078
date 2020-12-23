%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0yoqgB4NzH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 174 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  611 (2044 expanded)
%              Number of equality atoms :   14 (  64 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(t14_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                    = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                  & ( v1_tex_2 @ B @ A ) )
               => ( v1_tex_2 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                    & ( v1_tex_2 @ B @ A ) )
                 => ( v1_tex_2 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tex_2])).

thf('0',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( ( sk_C @ X17 @ X18 )
        = ( u1_struct_0 @ X17 ) )
      | ( v1_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( m1_pre_topc @ X16 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( m1_pre_topc @ X13 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ( m1_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['18','23'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('28',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('35',plain,
    ( ( m1_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('37',plain,(
    m1_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ( m1_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('41',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('45',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','47'])).

thf('49',plain,
    ( ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','48'])).

thf('50',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v1_subset_1 @ ( sk_C @ X17 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ( v1_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('53',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v1_tex_2 @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ( v1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_tex_2 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_tex_2 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['53','65','66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0yoqgB4NzH
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:19:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 88 iterations in 0.047s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.51  thf(t14_tex_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.51               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.51                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.21/0.51                   ( v1_tex_2 @ B @ A ) ) =>
% 0.21/0.51                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( l1_pre_topc @ A ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.51                  ( ( ( ( g1_pre_topc @
% 0.21/0.51                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.51                        ( g1_pre_topc @
% 0.21/0.51                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.21/0.51                      ( v1_tex_2 @ B @ A ) ) =>
% 0.21/0.51                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 0.21/0.51  thf('0', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d3_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ( v1_tex_2 @ B @ A ) <=>
% 0.21/0.51             ( ![C:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X17 @ X18)
% 0.21/0.51          | ((sk_C @ X17 @ X18) = (u1_struct_0 @ X17))
% 0.21/0.51          | (v1_tex_2 @ X17 @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.51        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t2_tsep_1, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X16 : $i]: ((m1_pre_topc @ X16 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.51  thf(t65_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( l1_pre_topc @ B ) =>
% 0.21/0.51           ( ( m1_pre_topc @ A @ B ) <=>
% 0.21/0.51             ( m1_pre_topc @
% 0.21/0.51               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X12)
% 0.21/0.51          | ~ (m1_pre_topc @ X13 @ X12)
% 0.21/0.51          | (m1_pre_topc @ X13 @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.21/0.51          | ~ (l1_pre_topc @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (m1_pre_topc @ X0 @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_pre_topc @ X0 @ 
% 0.21/0.51           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t59_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @
% 0.21/0.51             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.21/0.51           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X10 @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.51          | (m1_pre_topc @ X10 @ X11)
% 0.21/0.51          | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_C_1)
% 0.21/0.51          | (m1_pre_topc @ X0 @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.51          | (m1_pre_topc @ X0 @ sk_C_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.51  thf('18', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_B @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '17'])).
% 0.21/0.51  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('21', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '23'])).
% 0.21/0.51  thf(t1_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( m1_subset_1 @
% 0.21/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.51          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.51          | ~ (l1_pre_topc @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i]:
% 0.21/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_pre_topc @ X0 @ 
% 0.21/0.51           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((m1_pre_topc @ sk_C_1 @ 
% 0.21/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((m1_pre_topc @ sk_C_1 @ 
% 0.21/0.51        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X10 @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.51          | (m1_pre_topc @ X10 @ X11)
% 0.21/0.51          | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.51  thf('39', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_C_1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('41', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.51          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.51          | ~ (l1_pre_topc @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (((v1_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.51        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4', '48'])).
% 0.21/0.51  thf('50', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain, (((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X17 @ X18)
% 0.21/0.51          | ~ (v1_subset_1 @ (sk_C @ X17 @ X18) @ (u1_struct_0 @ X18))
% 0.21/0.51          | (v1_tex_2 @ X17 @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.51        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.51          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.51          | ~ (l1_pre_topc @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X17 @ X18)
% 0.21/0.51          | ~ (v1_tex_2 @ X17 @ X18)
% 0.21/0.51          | ((X19) != (u1_struct_0 @ X17))
% 0.21/0.51          | (v1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X18)
% 0.21/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.21/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | (v1_subset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))
% 0.21/0.51          | ~ (v1_tex_2 @ X17 @ X18)
% 0.21/0.51          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.21/0.51      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.51        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.51        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '60'])).
% 0.21/0.51  thf('62', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.21/0.51  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('67', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('68', plain, ((v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['53', '65', '66', '67'])).
% 0.21/0.51  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
