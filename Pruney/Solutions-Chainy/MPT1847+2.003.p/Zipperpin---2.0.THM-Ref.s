%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3DnNO2M7kK

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 316 expanded)
%              Number of leaves         :   27 ( 103 expanded)
%              Depth                    :   19
%              Number of atoms          :  682 (3676 expanded)
%              Number of equality atoms :   25 ( 136 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( sk_C @ X15 @ X16 )
        = ( u1_struct_0 @ X15 ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('5',plain,(
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

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ( ( m1_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['17','22'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( r1_tarski @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('27',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('37',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('44',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( r1_tarski @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('48',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['35','50'])).

thf('52',plain,
    ( ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','51'])).

thf('53',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v1_subset_1 @ ( sk_C @ X15 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('56',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_C @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('67',plain,
    ( ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v1_tex_2 @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ( v1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_tex_2 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['61','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3DnNO2M7kK
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:43:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 133 iterations in 0.049s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(t14_tex_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.49               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.49                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.21/0.49                   ( v1_tex_2 @ B @ A ) ) =>
% 0.21/0.49                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( l1_pre_topc @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.49                  ( ( ( ( g1_pre_topc @
% 0.21/0.49                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.21/0.49                        ( g1_pre_topc @
% 0.21/0.49                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.21/0.49                      ( v1_tex_2 @ B @ A ) ) =>
% 0.21/0.49                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 0.21/0.49  thf('0', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d3_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( ( v1_tex_2 @ B @ A ) <=>
% 0.21/0.49             ( ![C:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | ((sk_C @ X15 @ X16) = (u1_struct_0 @ X15))
% 0.21/0.49          | (v1_tex_2 @ X15 @ X16)
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.49        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t2_tsep_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X12 : $i]: ((m1_pre_topc @ X12 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.49  thf(t65_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_pre_topc @ B ) =>
% 0.21/0.49           ( ( m1_pre_topc @ A @ B ) <=>
% 0.21/0.49             ( m1_pre_topc @
% 0.21/0.49               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X10)
% 0.21/0.49          | ~ (m1_pre_topc @ X11 @ X10)
% 0.21/0.49          | (m1_pre_topc @ X11 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | (m1_pre_topc @ X0 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_pre_topc @ X0 @ 
% 0.21/0.49           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((m1_pre_topc @ sk_C_1 @ 
% 0.21/0.49         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['4', '8'])).
% 0.21/0.49  thf('10', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_m1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((m1_pre_topc @ sk_C_1 @ 
% 0.21/0.49        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.49  thf(t59_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @
% 0.21/0.49             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.21/0.49           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X8 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.21/0.49          | (m1_pre_topc @ X8 @ X9)
% 0.21/0.49          | ~ (l1_pre_topc @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.49  thf('17', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_C_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '22'])).
% 0.21/0.49  thf(t35_borsuk_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14))
% 0.21/0.49          | ~ (l1_pre_topc @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf(t28_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((k3_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))
% 0.21/0.49         = (u1_struct_0 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf(commutativity_k2_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.49  thf(t12_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.49         = (u1_struct_0 @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_pre_topc @ X0 @ 
% 0.21/0.49           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.21/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X8 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.21/0.49          | (m1_pre_topc @ X8 @ X9)
% 0.21/0.49          | ~ (l1_pre_topc @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.49          | ~ (l1_pre_topc @ sk_C_1)
% 0.21/0.49          | (m1_pre_topc @ X0 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.49          | (m1_pre_topc @ X0 @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '41'])).
% 0.21/0.49  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('44', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14))
% 0.21/0.49          | ~ (l1_pre_topc @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.49        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (((k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.49         = (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['35', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (((v1_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.49        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3', '51'])).
% 0.21/0.49  thf('53', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('54', plain, (((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | ~ (v1_subset_1 @ (sk_C @ X15 @ X16) @ (u1_struct_0 @ X16))
% 0.21/0.49          | (v1_tex_2 @ X15 @ X16)
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.49        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('58', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_tex_2 @ sk_C_1 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.49  thf('60', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | (m1_subset_1 @ (sk_C @ X15 @ X16) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.49          | (v1_tex_2 @ X15 @ X16)
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.49        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_A) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('66', plain, (((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((v1_tex_2 @ sk_C_1 @ sk_A)
% 0.21/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.49  thf('68', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | ~ (v1_tex_2 @ X15 @ X16)
% 0.21/0.49          | ((X17) != (u1_struct_0 @ X15))
% 0.21/0.49          | (v1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X16)
% 0.21/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.49          | (v1_subset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.21/0.49          | ~ (v1_tex_2 @ X15 @ X16)
% 0.21/0.49          | ~ (m1_pre_topc @ X15 @ X16))),
% 0.21/0.49      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.49        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.49        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['69', '71'])).
% 0.21/0.49  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('74', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.21/0.49  thf('77', plain, ($false), inference('demod', [status(thm)], ['61', '76'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
