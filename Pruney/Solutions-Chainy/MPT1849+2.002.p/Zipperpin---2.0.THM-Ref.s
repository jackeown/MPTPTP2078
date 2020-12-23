%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.54LttsW6Tx

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:57 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  257 (5798 expanded)
%              Number of leaves         :   36 (1717 expanded)
%              Depth                    :   25
%              Number of atoms          : 2230 (64829 expanded)
%              Number of equality atoms :  118 (3165 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t16_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
              = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['2','3'])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( m1_pre_topc @ X21 @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( ~ ( v1_pre_topc @ X3 )
      | ( X3
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('19',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( ( g1_pre_topc @ X16 @ X17 )
       != ( g1_pre_topc @ X14 @ X15 ) )
      | ( X16 = X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','28'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('30',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('51',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('53',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['31','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','57'])).

thf('59',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['2','3'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('64',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('67',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','67'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('70',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('71',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 = X32 )
      | ( v1_subset_1 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('72',plain,
    ( ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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

thf('74',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( ( sk_C @ X29 @ X30 )
        = ( u1_struct_0 @ X29 ) )
      | ( v1_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('78',plain,
    ( ( v1_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_subset_1 @ ( sk_C @ X29 @ X30 ) @ ( u1_struct_0 @ X30 ) )
      | ( v1_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('82',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('89',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','88'])).

thf('90',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('91',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('92',plain,(
    l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    ! [X3: $i] :
      ( ~ ( v1_pre_topc @ X3 )
      | ( X3
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( g1_pre_topc @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( ( g1_pre_topc @ X16 @ X17 )
       != ( g1_pre_topc @ X14 @ X15 ) )
      | ( X16 = X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','102'])).

thf('104',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( l1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( k2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','104'])).

thf('106',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('107',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('108',plain,
    ( ( k2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('109',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_struct_0 @ X6 )
       != X4 )
      | ( X6
        = ( k1_pre_topc @ X5 @ X4 ) )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( v1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('110',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( X6
        = ( k1_pre_topc @ X5 @ ( k2_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
        = ( k1_pre_topc @ X0 @ ( k2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,
    ( ( k2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('113',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
        = ( k1_pre_topc @ X0 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('116',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('117',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('118',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
        = ( k1_pre_topc @ X0 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','119'])).

thf('121',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('123',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('128',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('132',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('133',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ( m1_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['131','136'])).

thf('138',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('140',plain,(
    ! [X3: $i] :
      ( ~ ( v1_pre_topc @ X3 )
      | ( X3
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('141',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('142',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( ( g1_pre_topc @ X16 @ X17 )
       != ( g1_pre_topc @ X14 @ X15 ) )
      | ( X17 = X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['139','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( u1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['138','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( u1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('153',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','151','152'])).

thf('154',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('156',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('158',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( r1_tarski @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['156','160'])).

thf('162',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['155','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('166',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('170',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['168','170'])).

thf('172',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('175',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['173','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( X6
        = ( k1_pre_topc @ X5 @ ( k2_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( X0
        = ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) @ ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['153','182'])).

thf('184',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('185',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('187',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( l1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['185','188'])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( l1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('193',plain,
    ( ~ ( v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('196',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('200',plain,
    ( ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['193','198','199'])).

thf('201',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('202',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    = ( k1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['183','184','200','201'])).

thf('203',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('204',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('206',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('208',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('209',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('211',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('212',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','125','202','203','212'])).

thf('214',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('216',plain,(
    ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('218',plain,(
    ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['213','218'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.54LttsW6Tx
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.75/1.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.75/1.92  % Solved by: fo/fo7.sh
% 1.75/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.92  % done 3697 iterations in 1.465s
% 1.75/1.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.75/1.92  % SZS output start Refutation
% 1.75/1.92  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.75/1.92  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 1.75/1.92  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.75/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.92  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.75/1.92  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.75/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.75/1.92  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.75/1.92  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.75/1.92  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.75/1.92  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.75/1.92  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 1.75/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.75/1.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.75/1.92  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.75/1.92  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.75/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.75/1.92  thf(t16_tex_2, conjecture,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.75/1.92       ( ![B:$i]:
% 1.75/1.92         ( ( ( ~( v1_tex_2 @ B @ A ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.75/1.92           ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 1.75/1.92             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 1.75/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.92    (~( ![A:$i]:
% 1.75/1.92        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.75/1.92          ( ![B:$i]:
% 1.75/1.92            ( ( ( ~( v1_tex_2 @ B @ A ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.75/1.92              ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 1.75/1.92                ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )),
% 1.75/1.92    inference('cnf.neg', [status(esa)], [t16_tex_2])).
% 1.75/1.92  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf(t11_tmap_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( l1_pre_topc @ A ) =>
% 1.75/1.92       ( ![B:$i]:
% 1.75/1.92         ( ( m1_pre_topc @ B @ A ) =>
% 1.75/1.92           ( ( v1_pre_topc @
% 1.75/1.92               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 1.75/1.92             ( m1_pre_topc @
% 1.75/1.92               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 1.75/1.92  thf('1', plain,
% 1.75/1.92      (![X22 : $i, X23 : $i]:
% 1.75/1.92         (~ (m1_pre_topc @ X22 @ X23)
% 1.75/1.92          | (m1_pre_topc @ 
% 1.75/1.92             (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)) @ X23)
% 1.75/1.92          | ~ (l1_pre_topc @ X23))),
% 1.75/1.92      inference('cnf', [status(esa)], [t11_tmap_1])).
% 1.75/1.92  thf('2', plain,
% 1.75/1.92      ((~ (l1_pre_topc @ sk_A)
% 1.75/1.92        | (m1_pre_topc @ 
% 1.75/1.92           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A))),
% 1.75/1.92      inference('sup-', [status(thm)], ['0', '1'])).
% 1.75/1.92  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('4', plain,
% 1.75/1.92      ((m1_pre_topc @ 
% 1.75/1.92        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)),
% 1.75/1.92      inference('demod', [status(thm)], ['2', '3'])).
% 1.75/1.92  thf(t65_pre_topc, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( l1_pre_topc @ A ) =>
% 1.75/1.92       ( ![B:$i]:
% 1.75/1.92         ( ( l1_pre_topc @ B ) =>
% 1.75/1.92           ( ( m1_pre_topc @ A @ B ) <=>
% 1.75/1.92             ( m1_pre_topc @
% 1.75/1.92               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 1.75/1.92  thf('5', plain,
% 1.75/1.92      (![X20 : $i, X21 : $i]:
% 1.75/1.92         (~ (l1_pre_topc @ X20)
% 1.75/1.92          | ~ (m1_pre_topc @ X21 @ X20)
% 1.75/1.92          | (m1_pre_topc @ X21 @ 
% 1.75/1.92             (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 1.75/1.92          | ~ (l1_pre_topc @ X21))),
% 1.75/1.92      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.75/1.92  thf('6', plain,
% 1.75/1.92      ((~ (l1_pre_topc @ 
% 1.75/1.92           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.92        | (m1_pre_topc @ 
% 1.75/1.92           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.75/1.92           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.75/1.92        | ~ (l1_pre_topc @ sk_A))),
% 1.75/1.92      inference('sup-', [status(thm)], ['4', '5'])).
% 1.75/1.92  thf('7', plain,
% 1.75/1.92      ((m1_pre_topc @ 
% 1.75/1.92        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)),
% 1.75/1.93      inference('demod', [status(thm)], ['2', '3'])).
% 1.75/1.93  thf(dt_m1_pre_topc, axiom,
% 1.75/1.93    (![A:$i]:
% 1.75/1.93     ( ( l1_pre_topc @ A ) =>
% 1.75/1.93       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.75/1.93  thf('8', plain,
% 1.75/1.93      (![X11 : $i, X12 : $i]:
% 1.75/1.93         (~ (m1_pre_topc @ X11 @ X12)
% 1.75/1.93          | (l1_pre_topc @ X11)
% 1.75/1.93          | ~ (l1_pre_topc @ X12))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.75/1.93  thf('9', plain,
% 1.75/1.93      ((~ (l1_pre_topc @ sk_A)
% 1.75/1.93        | (l1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['7', '8'])).
% 1.75/1.93  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('11', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['9', '10'])).
% 1.75/1.93  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('13', plain,
% 1.75/1.93      ((m1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['6', '11', '12'])).
% 1.75/1.93  thf(d3_struct_0, axiom,
% 1.75/1.93    (![A:$i]:
% 1.75/1.93     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.75/1.93  thf('14', plain,
% 1.75/1.93      (![X7 : $i]:
% 1.75/1.93         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.75/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.75/1.93  thf(dt_u1_pre_topc, axiom,
% 1.75/1.93    (![A:$i]:
% 1.75/1.93     ( ( l1_pre_topc @ A ) =>
% 1.75/1.93       ( m1_subset_1 @
% 1.75/1.93         ( u1_pre_topc @ A ) @ 
% 1.75/1.93         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.75/1.93  thf('15', plain,
% 1.75/1.93      (![X13 : $i]:
% 1.75/1.93         ((m1_subset_1 @ (u1_pre_topc @ X13) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 1.75/1.93          | ~ (l1_pre_topc @ X13))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.75/1.93  thf(dt_g1_pre_topc, axiom,
% 1.75/1.93    (![A:$i,B:$i]:
% 1.75/1.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.75/1.93       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 1.75/1.93         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 1.75/1.93  thf('16', plain,
% 1.75/1.93      (![X8 : $i, X9 : $i]:
% 1.75/1.93         ((v1_pre_topc @ (g1_pre_topc @ X8 @ X9))
% 1.75/1.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 1.75/1.93  thf('17', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (v1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['15', '16'])).
% 1.75/1.93  thf(abstractness_v1_pre_topc, axiom,
% 1.75/1.93    (![A:$i]:
% 1.75/1.93     ( ( l1_pre_topc @ A ) =>
% 1.75/1.93       ( ( v1_pre_topc @ A ) =>
% 1.75/1.93         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.75/1.93  thf('18', plain,
% 1.75/1.93      (![X3 : $i]:
% 1.75/1.93         (~ (v1_pre_topc @ X3)
% 1.75/1.93          | ((X3) = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 1.75/1.93          | ~ (l1_pre_topc @ X3))),
% 1.75/1.93      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.75/1.93  thf('19', plain,
% 1.75/1.93      (![X13 : $i]:
% 1.75/1.93         ((m1_subset_1 @ (u1_pre_topc @ X13) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 1.75/1.93          | ~ (l1_pre_topc @ X13))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.75/1.93  thf(free_g1_pre_topc, axiom,
% 1.75/1.93    (![A:$i,B:$i]:
% 1.75/1.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.75/1.93       ( ![C:$i,D:$i]:
% 1.75/1.93         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 1.75/1.93           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 1.75/1.93  thf('20', plain,
% 1.75/1.93      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.75/1.93         (((g1_pre_topc @ X16 @ X17) != (g1_pre_topc @ X14 @ X15))
% 1.75/1.93          | ((X16) = (X14))
% 1.75/1.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 1.75/1.93      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.75/1.93  thf('21', plain,
% 1.75/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ((u1_struct_0 @ X0) = (X1))
% 1.75/1.93          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.75/1.93              != (g1_pre_topc @ X1 @ X2)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['19', '20'])).
% 1.75/1.93  thf('22', plain,
% 1.75/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.93         (((X0) != (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (v1_pre_topc @ X0)
% 1.75/1.93          | ((u1_struct_0 @ X0) = (X2))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup-', [status(thm)], ['18', '21'])).
% 1.75/1.93  thf('23', plain,
% 1.75/1.93      (![X1 : $i, X2 : $i]:
% 1.75/1.93         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.75/1.93          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.75/1.93      inference('simplify', [status(thm)], ['22'])).
% 1.75/1.93  thf('24', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ 
% 1.75/1.93               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93          | ((u1_struct_0 @ 
% 1.75/1.93              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93              = (u1_struct_0 @ X0)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['17', '23'])).
% 1.75/1.93  thf('25', plain,
% 1.75/1.93      (![X13 : $i]:
% 1.75/1.93         ((m1_subset_1 @ (u1_pre_topc @ X13) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 1.75/1.93          | ~ (l1_pre_topc @ X13))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.75/1.93  thf('26', plain,
% 1.75/1.93      (![X8 : $i, X9 : $i]:
% 1.75/1.93         ((l1_pre_topc @ (g1_pre_topc @ X8 @ X9))
% 1.75/1.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 1.75/1.93  thf('27', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['25', '26'])).
% 1.75/1.93  thf('28', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (((u1_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93            = (u1_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('clc', [status(thm)], ['24', '27'])).
% 1.75/1.93  thf('29', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (((u1_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93            = (u1_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_struct_0 @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup+', [status(thm)], ['14', '28'])).
% 1.75/1.93  thf(dt_l1_pre_topc, axiom,
% 1.75/1.93    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.75/1.93  thf('30', plain,
% 1.75/1.93      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.75/1.93  thf('31', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ((u1_struct_0 @ 
% 1.75/1.93              (g1_pre_topc @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93              = (u1_struct_0 @ X0)))),
% 1.75/1.93      inference('clc', [status(thm)], ['29', '30'])).
% 1.75/1.93  thf('32', plain,
% 1.75/1.93      (![X7 : $i]:
% 1.75/1.93         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.75/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.75/1.93  thf('33', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('34', plain,
% 1.75/1.93      (![X22 : $i, X23 : $i]:
% 1.75/1.93         (~ (m1_pre_topc @ X22 @ X23)
% 1.75/1.93          | (v1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 1.75/1.93          | ~ (l1_pre_topc @ X23))),
% 1.75/1.93      inference('cnf', [status(esa)], [t11_tmap_1])).
% 1.75/1.93  thf('35', plain,
% 1.75/1.93      ((~ (l1_pre_topc @ sk_A)
% 1.75/1.93        | (v1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['33', '34'])).
% 1.75/1.93  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('37', plain,
% 1.75/1.93      ((v1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['35', '36'])).
% 1.75/1.93  thf('38', plain,
% 1.75/1.93      (((v1_pre_topc @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93        | ~ (l1_struct_0 @ sk_B))),
% 1.75/1.93      inference('sup+', [status(thm)], ['32', '37'])).
% 1.75/1.93  thf('39', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('40', plain,
% 1.75/1.93      (![X11 : $i, X12 : $i]:
% 1.75/1.93         (~ (m1_pre_topc @ X11 @ X12)
% 1.75/1.93          | (l1_pre_topc @ X11)
% 1.75/1.93          | ~ (l1_pre_topc @ X12))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.75/1.93  thf('41', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.75/1.93      inference('sup-', [status(thm)], ['39', '40'])).
% 1.75/1.93  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 1.75/1.93      inference('demod', [status(thm)], ['41', '42'])).
% 1.75/1.93  thf('44', plain,
% 1.75/1.93      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.75/1.93  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 1.75/1.93      inference('sup-', [status(thm)], ['43', '44'])).
% 1.75/1.93  thf('46', plain,
% 1.75/1.93      ((v1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['38', '45'])).
% 1.75/1.93  thf('47', plain,
% 1.75/1.93      (![X1 : $i, X2 : $i]:
% 1.75/1.93         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.75/1.93          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.75/1.93      inference('simplify', [status(thm)], ['22'])).
% 1.75/1.93  thf('48', plain,
% 1.75/1.93      ((~ (l1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93        | ((u1_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93            = (k2_struct_0 @ sk_B)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['46', '47'])).
% 1.75/1.93  thf('49', plain,
% 1.75/1.93      (![X7 : $i]:
% 1.75/1.93         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.75/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.75/1.93  thf('50', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['9', '10'])).
% 1.75/1.93  thf('51', plain,
% 1.75/1.93      (((l1_pre_topc @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93        | ~ (l1_struct_0 @ sk_B))),
% 1.75/1.93      inference('sup+', [status(thm)], ['49', '50'])).
% 1.75/1.93  thf('52', plain, ((l1_struct_0 @ sk_B)),
% 1.75/1.93      inference('sup-', [status(thm)], ['43', '44'])).
% 1.75/1.93  thf('53', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['51', '52'])).
% 1.75/1.93  thf('54', plain,
% 1.75/1.93      (((u1_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93         = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['48', '53'])).
% 1.75/1.93  thf('55', plain,
% 1.75/1.93      ((((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B)) | ~ (l1_pre_topc @ sk_B))),
% 1.75/1.93      inference('sup+', [status(thm)], ['31', '54'])).
% 1.75/1.93  thf('56', plain, ((l1_pre_topc @ sk_B)),
% 1.75/1.93      inference('demod', [status(thm)], ['41', '42'])).
% 1.75/1.93  thf('57', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('58', plain,
% 1.75/1.93      ((m1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['13', '57'])).
% 1.75/1.93  thf('59', plain,
% 1.75/1.93      ((m1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)),
% 1.75/1.93      inference('demod', [status(thm)], ['2', '3'])).
% 1.75/1.93  thf(t1_tsep_1, axiom,
% 1.75/1.93    (![A:$i]:
% 1.75/1.93     ( ( l1_pre_topc @ A ) =>
% 1.75/1.93       ( ![B:$i]:
% 1.75/1.93         ( ( m1_pre_topc @ B @ A ) =>
% 1.75/1.93           ( m1_subset_1 @
% 1.75/1.93             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.75/1.93  thf('60', plain,
% 1.75/1.93      (![X24 : $i, X25 : $i]:
% 1.75/1.93         (~ (m1_pre_topc @ X24 @ X25)
% 1.75/1.93          | (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 1.75/1.93             (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.75/1.93          | ~ (l1_pre_topc @ X25))),
% 1.75/1.93      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.75/1.93  thf('61', plain,
% 1.75/1.93      ((~ (l1_pre_topc @ sk_A)
% 1.75/1.93        | (m1_subset_1 @ 
% 1.75/1.93           (u1_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['59', '60'])).
% 1.75/1.93  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('63', plain,
% 1.75/1.93      ((v1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['35', '36'])).
% 1.75/1.93  thf('64', plain,
% 1.75/1.93      (![X1 : $i, X2 : $i]:
% 1.75/1.93         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.75/1.93          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.75/1.93      inference('simplify', [status(thm)], ['22'])).
% 1.75/1.93  thf('65', plain,
% 1.75/1.93      ((~ (l1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93        | ((u1_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93            = (u1_struct_0 @ sk_B)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['63', '64'])).
% 1.75/1.93  thf('66', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['9', '10'])).
% 1.75/1.93  thf('67', plain,
% 1.75/1.93      (((u1_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93         = (u1_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['65', '66'])).
% 1.75/1.93  thf('68', plain,
% 1.75/1.93      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.75/1.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['61', '62', '67'])).
% 1.75/1.93  thf('69', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('70', plain,
% 1.75/1.93      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 1.75/1.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['68', '69'])).
% 1.75/1.93  thf(d7_subset_1, axiom,
% 1.75/1.93    (![A:$i,B:$i]:
% 1.75/1.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.75/1.93       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 1.75/1.93  thf('71', plain,
% 1.75/1.93      (![X32 : $i, X33 : $i]:
% 1.75/1.93         (((X33) = (X32))
% 1.75/1.93          | (v1_subset_1 @ X33 @ X32)
% 1.75/1.93          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 1.75/1.93      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.75/1.93  thf('72', plain,
% 1.75/1.93      (((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.75/1.93        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['70', '71'])).
% 1.75/1.93  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf(d3_tex_2, axiom,
% 1.75/1.93    (![A:$i]:
% 1.75/1.93     ( ( l1_pre_topc @ A ) =>
% 1.75/1.93       ( ![B:$i]:
% 1.75/1.93         ( ( m1_pre_topc @ B @ A ) =>
% 1.75/1.93           ( ( v1_tex_2 @ B @ A ) <=>
% 1.75/1.93             ( ![C:$i]:
% 1.75/1.93               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.75/1.93                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.75/1.93                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.75/1.93  thf('74', plain,
% 1.75/1.93      (![X29 : $i, X30 : $i]:
% 1.75/1.93         (~ (m1_pre_topc @ X29 @ X30)
% 1.75/1.93          | ((sk_C @ X29 @ X30) = (u1_struct_0 @ X29))
% 1.75/1.93          | (v1_tex_2 @ X29 @ X30)
% 1.75/1.93          | ~ (l1_pre_topc @ X30))),
% 1.75/1.93      inference('cnf', [status(esa)], [d3_tex_2])).
% 1.75/1.93  thf('75', plain,
% 1.75/1.93      ((~ (l1_pre_topc @ sk_A)
% 1.75/1.93        | (v1_tex_2 @ sk_B @ sk_A)
% 1.75/1.93        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['73', '74'])).
% 1.75/1.93  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('77', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('78', plain,
% 1.75/1.93      (((v1_tex_2 @ sk_B @ sk_A)
% 1.75/1.93        | ((sk_C @ sk_B @ sk_A) = (k2_struct_0 @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.75/1.93  thf('79', plain, (~ (v1_tex_2 @ sk_B @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('80', plain, (((sk_C @ sk_B @ sk_A) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('clc', [status(thm)], ['78', '79'])).
% 1.75/1.93  thf('81', plain,
% 1.75/1.93      (![X29 : $i, X30 : $i]:
% 1.75/1.93         (~ (m1_pre_topc @ X29 @ X30)
% 1.75/1.93          | ~ (v1_subset_1 @ (sk_C @ X29 @ X30) @ (u1_struct_0 @ X30))
% 1.75/1.93          | (v1_tex_2 @ X29 @ X30)
% 1.75/1.93          | ~ (l1_pre_topc @ X30))),
% 1.75/1.93      inference('cnf', [status(esa)], [d3_tex_2])).
% 1.75/1.93  thf('82', plain,
% 1.75/1.93      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.75/1.93        | ~ (l1_pre_topc @ sk_A)
% 1.75/1.93        | (v1_tex_2 @ sk_B @ sk_A)
% 1.75/1.93        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.75/1.93      inference('sup-', [status(thm)], ['80', '81'])).
% 1.75/1.93  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('84', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('85', plain,
% 1.75/1.93      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.75/1.93        | (v1_tex_2 @ sk_B @ sk_A))),
% 1.75/1.93      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.75/1.93  thf('86', plain, (~ (v1_tex_2 @ sk_B @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('87', plain,
% 1.75/1.93      (~ (v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.75/1.93      inference('clc', [status(thm)], ['85', '86'])).
% 1.75/1.93  thf('88', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.75/1.93      inference('sup-', [status(thm)], ['72', '87'])).
% 1.75/1.93  thf('89', plain,
% 1.75/1.93      ((m1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['58', '88'])).
% 1.75/1.93  thf('90', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['9', '10'])).
% 1.75/1.93  thf('91', plain,
% 1.75/1.93      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.75/1.93  thf('92', plain,
% 1.75/1.93      ((l1_struct_0 @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['90', '91'])).
% 1.75/1.93  thf('93', plain,
% 1.75/1.93      (![X7 : $i]:
% 1.75/1.93         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.75/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.75/1.93  thf('94', plain,
% 1.75/1.93      (![X3 : $i]:
% 1.75/1.93         (~ (v1_pre_topc @ X3)
% 1.75/1.93          | ((X3) = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 1.75/1.93          | ~ (l1_pre_topc @ X3))),
% 1.75/1.93      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.75/1.93  thf('95', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (((X0) = (g1_pre_topc @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93          | ~ (l1_struct_0 @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (v1_pre_topc @ X0))),
% 1.75/1.93      inference('sup+', [status(thm)], ['93', '94'])).
% 1.75/1.93  thf('96', plain,
% 1.75/1.93      (![X7 : $i]:
% 1.75/1.93         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.75/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.75/1.93  thf('97', plain,
% 1.75/1.93      (![X13 : $i]:
% 1.75/1.93         ((m1_subset_1 @ (u1_pre_topc @ X13) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 1.75/1.93          | ~ (l1_pre_topc @ X13))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.75/1.93  thf('98', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))
% 1.75/1.93          | ~ (l1_struct_0 @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup+', [status(thm)], ['96', '97'])).
% 1.75/1.93  thf('99', plain,
% 1.75/1.93      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.75/1.93  thf('100', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 1.75/1.93             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))))),
% 1.75/1.93      inference('clc', [status(thm)], ['98', '99'])).
% 1.75/1.93  thf('101', plain,
% 1.75/1.93      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.75/1.93         (((g1_pre_topc @ X16 @ X17) != (g1_pre_topc @ X14 @ X15))
% 1.75/1.93          | ((X16) = (X14))
% 1.75/1.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 1.75/1.93      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.75/1.93  thf('102', plain,
% 1.75/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ((k2_struct_0 @ X0) = (X1))
% 1.75/1.93          | ((g1_pre_topc @ (k2_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.75/1.93              != (g1_pre_topc @ X1 @ X2)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['100', '101'])).
% 1.75/1.93  thf('103', plain,
% 1.75/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.93         (((X0) != (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (v1_pre_topc @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (l1_struct_0 @ X0)
% 1.75/1.93          | ((k2_struct_0 @ X0) = (X2))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup-', [status(thm)], ['95', '102'])).
% 1.75/1.93  thf('104', plain,
% 1.75/1.93      (![X1 : $i, X2 : $i]:
% 1.75/1.93         (((k2_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.75/1.93          | ~ (l1_struct_0 @ (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.75/1.93      inference('simplify', [status(thm)], ['103'])).
% 1.75/1.93  thf('105', plain,
% 1.75/1.93      ((~ (v1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93        | ~ (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93        | ((k2_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93            = (u1_struct_0 @ sk_B)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['92', '104'])).
% 1.75/1.93  thf('106', plain,
% 1.75/1.93      ((v1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['35', '36'])).
% 1.75/1.93  thf('107', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['9', '10'])).
% 1.75/1.93  thf('108', plain,
% 1.75/1.93      (((k2_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93         = (u1_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['105', '106', '107'])).
% 1.75/1.93  thf(d10_pre_topc, axiom,
% 1.75/1.93    (![A:$i]:
% 1.75/1.93     ( ( l1_pre_topc @ A ) =>
% 1.75/1.93       ( ![B:$i]:
% 1.75/1.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.75/1.93           ( ![C:$i]:
% 1.75/1.93             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.75/1.93               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 1.75/1.93                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 1.75/1.93  thf('109', plain,
% 1.75/1.93      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.75/1.93         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 1.75/1.93          | ((k2_struct_0 @ X6) != (X4))
% 1.75/1.93          | ((X6) = (k1_pre_topc @ X5 @ X4))
% 1.75/1.93          | ~ (m1_pre_topc @ X6 @ X5)
% 1.75/1.93          | ~ (v1_pre_topc @ X6)
% 1.75/1.93          | ~ (l1_pre_topc @ X5))),
% 1.75/1.93      inference('cnf', [status(esa)], [d10_pre_topc])).
% 1.75/1.93  thf('110', plain,
% 1.75/1.93      (![X5 : $i, X6 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X5)
% 1.75/1.93          | ~ (v1_pre_topc @ X6)
% 1.75/1.93          | ~ (m1_pre_topc @ X6 @ X5)
% 1.75/1.93          | ((X6) = (k1_pre_topc @ X5 @ (k2_struct_0 @ X6)))
% 1.75/1.93          | ~ (m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 1.75/1.93               (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 1.75/1.93      inference('simplify', [status(thm)], ['109'])).
% 1.75/1.93  thf('111', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.75/1.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.75/1.93          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 1.75/1.93              = (k1_pre_topc @ X0 @ 
% 1.75/1.93                 (k2_struct_0 @ 
% 1.75/1.93                  (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.75/1.93          | ~ (m1_pre_topc @ 
% 1.75/1.93               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 1.75/1.93          | ~ (v1_pre_topc @ 
% 1.75/1.93               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup-', [status(thm)], ['108', '110'])).
% 1.75/1.93  thf('112', plain,
% 1.75/1.93      (((k2_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93         = (u1_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['105', '106', '107'])).
% 1.75/1.93  thf('113', plain,
% 1.75/1.93      ((v1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['35', '36'])).
% 1.75/1.93  thf('114', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.75/1.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.75/1.93          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 1.75/1.93              = (k1_pre_topc @ X0 @ (u1_struct_0 @ sk_B)))
% 1.75/1.93          | ~ (m1_pre_topc @ 
% 1.75/1.93               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('demod', [status(thm)], ['111', '112', '113'])).
% 1.75/1.93  thf('115', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('116', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('117', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('118', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('119', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 1.75/1.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.75/1.93          | ((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 1.75/1.93              = (k1_pre_topc @ X0 @ (k2_struct_0 @ sk_B)))
% 1.75/1.93          | ~ (m1_pre_topc @ 
% 1.75/1.93               (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 1.75/1.93  thf('120', plain,
% 1.75/1.93      ((~ (l1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93        | ((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 1.75/1.93            = (k1_pre_topc @ 
% 1.75/1.93               (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)) @ 
% 1.75/1.93               (k2_struct_0 @ sk_B)))
% 1.75/1.93        | ~ (m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 1.75/1.93             (k1_zfmisc_1 @ 
% 1.75/1.93              (u1_struct_0 @ 
% 1.75/1.93               (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['89', '119'])).
% 1.75/1.93  thf('121', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.75/1.93      inference('sup-', [status(thm)], ['72', '87'])).
% 1.75/1.93  thf('122', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['25', '26'])).
% 1.75/1.93  thf('123', plain,
% 1.75/1.93      (((l1_pre_topc @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93        | ~ (l1_pre_topc @ sk_A))),
% 1.75/1.93      inference('sup+', [status(thm)], ['121', '122'])).
% 1.75/1.93  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('125', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['123', '124'])).
% 1.75/1.93  thf('126', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.75/1.93      inference('sup-', [status(thm)], ['72', '87'])).
% 1.75/1.93  thf('127', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (((u1_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93            = (u1_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('clc', [status(thm)], ['24', '27'])).
% 1.75/1.93  thf('128', plain,
% 1.75/1.93      ((((u1_struct_0 @ 
% 1.75/1.93          (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93          = (u1_struct_0 @ sk_A))
% 1.75/1.93        | ~ (l1_pre_topc @ sk_A))),
% 1.75/1.93      inference('sup+', [status(thm)], ['126', '127'])).
% 1.75/1.93  thf('129', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.75/1.93      inference('sup-', [status(thm)], ['72', '87'])).
% 1.75/1.93  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('131', plain,
% 1.75/1.93      (((u1_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93         = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['128', '129', '130'])).
% 1.75/1.93  thf(t2_tsep_1, axiom,
% 1.75/1.93    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.75/1.93  thf('132', plain,
% 1.75/1.93      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.75/1.93      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.75/1.93  thf(t59_pre_topc, axiom,
% 1.75/1.93    (![A:$i]:
% 1.75/1.93     ( ( l1_pre_topc @ A ) =>
% 1.75/1.93       ( ![B:$i]:
% 1.75/1.93         ( ( m1_pre_topc @
% 1.75/1.93             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 1.75/1.93           ( m1_pre_topc @ B @ A ) ) ) ))).
% 1.75/1.93  thf('133', plain,
% 1.75/1.93      (![X18 : $i, X19 : $i]:
% 1.75/1.93         (~ (m1_pre_topc @ X18 @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 1.75/1.93          | (m1_pre_topc @ X18 @ X19)
% 1.75/1.93          | ~ (l1_pre_topc @ X19))),
% 1.75/1.93      inference('cnf', [status(esa)], [t59_pre_topc])).
% 1.75/1.93  thf('134', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93          | ~ (l1_pre_topc @ X0)
% 1.75/1.93          | (m1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 1.75/1.93      inference('sup-', [status(thm)], ['132', '133'])).
% 1.75/1.93  thf('135', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['25', '26'])).
% 1.75/1.93  thf('136', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         ((m1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('clc', [status(thm)], ['134', '135'])).
% 1.75/1.93  thf('137', plain,
% 1.75/1.93      (((m1_pre_topc @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ 
% 1.75/1.93          (u1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))) @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93        | ~ (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))),
% 1.75/1.93      inference('sup+', [status(thm)], ['131', '136'])).
% 1.75/1.93  thf('138', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.75/1.93      inference('sup-', [status(thm)], ['72', '87'])).
% 1.75/1.93  thf('139', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (v1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['15', '16'])).
% 1.75/1.93  thf('140', plain,
% 1.75/1.93      (![X3 : $i]:
% 1.75/1.93         (~ (v1_pre_topc @ X3)
% 1.75/1.93          | ((X3) = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 1.75/1.93          | ~ (l1_pre_topc @ X3))),
% 1.75/1.93      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.75/1.93  thf('141', plain,
% 1.75/1.93      (![X13 : $i]:
% 1.75/1.93         ((m1_subset_1 @ (u1_pre_topc @ X13) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 1.75/1.93          | ~ (l1_pre_topc @ X13))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.75/1.93  thf('142', plain,
% 1.75/1.93      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.75/1.93         (((g1_pre_topc @ X16 @ X17) != (g1_pre_topc @ X14 @ X15))
% 1.75/1.93          | ((X17) = (X15))
% 1.75/1.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 1.75/1.93      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.75/1.93  thf('143', plain,
% 1.75/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ((u1_pre_topc @ X0) = (X1))
% 1.75/1.93          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.75/1.93              != (g1_pre_topc @ X2 @ X1)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['141', '142'])).
% 1.75/1.93  thf('144', plain,
% 1.75/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.93         (((X0) != (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (v1_pre_topc @ X0)
% 1.75/1.93          | ((u1_pre_topc @ X0) = (X1))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup-', [status(thm)], ['140', '143'])).
% 1.75/1.93  thf('145', plain,
% 1.75/1.93      (![X1 : $i, X2 : $i]:
% 1.75/1.93         (((u1_pre_topc @ (g1_pre_topc @ X2 @ X1)) = (X1))
% 1.75/1.93          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.75/1.93      inference('simplify', [status(thm)], ['144'])).
% 1.75/1.93  thf('146', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ 
% 1.75/1.93               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93          | ((u1_pre_topc @ 
% 1.75/1.93              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93              = (u1_pre_topc @ X0)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['139', '145'])).
% 1.75/1.93  thf('147', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['25', '26'])).
% 1.75/1.93  thf('148', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (((u1_pre_topc @ 
% 1.75/1.93            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93            = (u1_pre_topc @ X0))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('clc', [status(thm)], ['146', '147'])).
% 1.75/1.93  thf('149', plain,
% 1.75/1.93      ((((u1_pre_topc @ 
% 1.75/1.93          (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93          = (u1_pre_topc @ sk_A))
% 1.75/1.93        | ~ (l1_pre_topc @ sk_A))),
% 1.75/1.93      inference('sup+', [status(thm)], ['138', '148'])).
% 1.75/1.93  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('151', plain,
% 1.75/1.93      (((u1_pre_topc @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93         = (u1_pre_topc @ sk_A))),
% 1.75/1.93      inference('demod', [status(thm)], ['149', '150'])).
% 1.75/1.93  thf('152', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['123', '124'])).
% 1.75/1.93  thf('153', plain,
% 1.75/1.93      ((m1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)) @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['137', '151', '152'])).
% 1.75/1.93  thf('154', plain,
% 1.75/1.93      (![X7 : $i]:
% 1.75/1.93         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.75/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.75/1.93  thf('155', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (((u1_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.75/1.93            = (u1_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('clc', [status(thm)], ['24', '27'])).
% 1.75/1.93  thf('156', plain,
% 1.75/1.93      (![X7 : $i]:
% 1.75/1.93         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.75/1.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.75/1.93  thf('157', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         ((m1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('clc', [status(thm)], ['134', '135'])).
% 1.75/1.93  thf(t35_borsuk_1, axiom,
% 1.75/1.93    (![A:$i]:
% 1.75/1.93     ( ( l1_pre_topc @ A ) =>
% 1.75/1.93       ( ![B:$i]:
% 1.75/1.93         ( ( m1_pre_topc @ B @ A ) =>
% 1.75/1.93           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.75/1.93  thf('158', plain,
% 1.75/1.93      (![X27 : $i, X28 : $i]:
% 1.75/1.93         (~ (m1_pre_topc @ X27 @ X28)
% 1.75/1.93          | (r1_tarski @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 1.75/1.93          | ~ (l1_pre_topc @ X28))),
% 1.75/1.93      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.75/1.93  thf('159', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0)
% 1.75/1.93          | (r1_tarski @ 
% 1.75/1.93             (u1_struct_0 @ 
% 1.75/1.93              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 1.75/1.93             (u1_struct_0 @ X0)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['157', '158'])).
% 1.75/1.93  thf('160', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         ((r1_tarski @ 
% 1.75/1.93           (u1_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 1.75/1.93           (u1_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('simplify', [status(thm)], ['159'])).
% 1.75/1.93  thf('161', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         ((r1_tarski @ 
% 1.75/1.93           (u1_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 1.75/1.93           (k2_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_struct_0 @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup+', [status(thm)], ['156', '160'])).
% 1.75/1.93  thf('162', plain,
% 1.75/1.93      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.75/1.93  thf('163', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (r1_tarski @ 
% 1.75/1.93             (u1_struct_0 @ 
% 1.75/1.93              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 1.75/1.93             (k2_struct_0 @ X0)))),
% 1.75/1.93      inference('clc', [status(thm)], ['161', '162'])).
% 1.75/1.93  thf('164', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         ((r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup+', [status(thm)], ['155', '163'])).
% 1.75/1.93  thf('165', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 1.75/1.93      inference('simplify', [status(thm)], ['164'])).
% 1.75/1.93  thf(d10_xboole_0, axiom,
% 1.75/1.93    (![A:$i,B:$i]:
% 1.75/1.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.75/1.93  thf('166', plain,
% 1.75/1.93      (![X0 : $i, X2 : $i]:
% 1.75/1.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.75/1.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.75/1.93  thf('167', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 1.75/1.93          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['165', '166'])).
% 1.75/1.93  thf('168', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_struct_0 @ X0)
% 1.75/1.93          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup-', [status(thm)], ['154', '167'])).
% 1.75/1.93  thf('169', plain,
% 1.75/1.93      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.75/1.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.75/1.93  thf('170', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.75/1.93      inference('simplify', [status(thm)], ['169'])).
% 1.75/1.93  thf('171', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_struct_0 @ X0)
% 1.75/1.93          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('demod', [status(thm)], ['168', '170'])).
% 1.75/1.93  thf('172', plain,
% 1.75/1.93      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.75/1.93  thf('173', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 1.75/1.93      inference('clc', [status(thm)], ['171', '172'])).
% 1.75/1.93  thf('174', plain,
% 1.75/1.93      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.75/1.93      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.75/1.93  thf('175', plain,
% 1.75/1.93      (![X24 : $i, X25 : $i]:
% 1.75/1.93         (~ (m1_pre_topc @ X24 @ X25)
% 1.75/1.93          | (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 1.75/1.93             (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.75/1.93          | ~ (l1_pre_topc @ X25))),
% 1.75/1.93      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.75/1.93  thf('176', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0)
% 1.75/1.93          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.75/1.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['174', '175'])).
% 1.75/1.93  thf('177', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('simplify', [status(thm)], ['176'])).
% 1.75/1.93  thf('178', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.75/1.93          | ~ (l1_pre_topc @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup+', [status(thm)], ['173', '177'])).
% 1.75/1.93  thf('179', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 1.75/1.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.75/1.93      inference('simplify', [status(thm)], ['178'])).
% 1.75/1.93  thf('180', plain,
% 1.75/1.93      (![X5 : $i, X6 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X5)
% 1.75/1.93          | ~ (v1_pre_topc @ X6)
% 1.75/1.93          | ~ (m1_pre_topc @ X6 @ X5)
% 1.75/1.93          | ((X6) = (k1_pre_topc @ X5 @ (k2_struct_0 @ X6)))
% 1.75/1.93          | ~ (m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 1.75/1.93               (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 1.75/1.93      inference('simplify', [status(thm)], ['109'])).
% 1.75/1.93  thf('181', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | ((X0) = (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 1.75/1.93          | ~ (m1_pre_topc @ X0 @ X0)
% 1.75/1.93          | ~ (v1_pre_topc @ X0)
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('sup-', [status(thm)], ['179', '180'])).
% 1.75/1.93  thf('182', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (v1_pre_topc @ X0)
% 1.75/1.93          | ~ (m1_pre_topc @ X0 @ X0)
% 1.75/1.93          | ((X0) = (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('simplify', [status(thm)], ['181'])).
% 1.75/1.93  thf('183', plain,
% 1.75/1.93      ((~ (l1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93        | ((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.75/1.93            = (k1_pre_topc @ 
% 1.75/1.93               (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)) @ 
% 1.75/1.93               (k2_struct_0 @ 
% 1.75/1.93                (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))))
% 1.75/1.93        | ~ (v1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['153', '182'])).
% 1.75/1.93  thf('184', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['123', '124'])).
% 1.75/1.93  thf('185', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.75/1.93      inference('sup-', [status(thm)], ['72', '87'])).
% 1.75/1.93  thf('186', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['25', '26'])).
% 1.75/1.93  thf('187', plain,
% 1.75/1.93      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.75/1.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.75/1.93  thf('188', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (l1_struct_0 @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['186', '187'])).
% 1.75/1.93  thf('189', plain,
% 1.75/1.93      (((l1_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93        | ~ (l1_pre_topc @ sk_A))),
% 1.75/1.93      inference('sup+', [status(thm)], ['185', '188'])).
% 1.75/1.93  thf('190', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('191', plain,
% 1.75/1.93      ((l1_struct_0 @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['189', '190'])).
% 1.75/1.93  thf('192', plain,
% 1.75/1.93      (![X1 : $i, X2 : $i]:
% 1.75/1.93         (((k2_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.75/1.93          | ~ (l1_struct_0 @ (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.75/1.93          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.75/1.93      inference('simplify', [status(thm)], ['103'])).
% 1.75/1.93  thf('193', plain,
% 1.75/1.93      ((~ (v1_pre_topc @ 
% 1.75/1.93           (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93        | ~ (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93        | ((k2_struct_0 @ 
% 1.75/1.93            (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93            = (k2_struct_0 @ sk_B)))),
% 1.75/1.93      inference('sup-', [status(thm)], ['191', '192'])).
% 1.75/1.93  thf('194', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.75/1.93      inference('sup-', [status(thm)], ['72', '87'])).
% 1.75/1.93  thf('195', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         (~ (l1_pre_topc @ X0)
% 1.75/1.93          | (v1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.75/1.93      inference('sup-', [status(thm)], ['15', '16'])).
% 1.75/1.93  thf('196', plain,
% 1.75/1.93      (((v1_pre_topc @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93        | ~ (l1_pre_topc @ sk_A))),
% 1.75/1.93      inference('sup+', [status(thm)], ['194', '195'])).
% 1.75/1.93  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('198', plain,
% 1.75/1.93      ((v1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['196', '197'])).
% 1.75/1.93  thf('199', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['123', '124'])).
% 1.75/1.93  thf('200', plain,
% 1.75/1.93      (((k2_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93         = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['193', '198', '199'])).
% 1.75/1.93  thf('201', plain,
% 1.75/1.93      ((v1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['196', '197'])).
% 1.75/1.93  thf('202', plain,
% 1.75/1.93      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.75/1.93         = (k1_pre_topc @ 
% 1.75/1.93            (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)) @ 
% 1.75/1.93            (k2_struct_0 @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['183', '184', '200', '201'])).
% 1.75/1.93  thf('203', plain,
% 1.75/1.93      (((u1_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.75/1.93         = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['128', '129', '130'])).
% 1.75/1.93  thf('204', plain,
% 1.75/1.93      (((u1_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93         = (u1_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['65', '66'])).
% 1.75/1.93  thf('205', plain,
% 1.75/1.93      (![X0 : $i]:
% 1.75/1.93         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.75/1.93           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.75/1.93          | ~ (l1_pre_topc @ X0))),
% 1.75/1.93      inference('simplify', [status(thm)], ['176'])).
% 1.75/1.93  thf('206', plain,
% 1.75/1.93      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.75/1.93         (k1_zfmisc_1 @ 
% 1.75/1.93          (u1_struct_0 @ 
% 1.75/1.93           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 1.75/1.93        | ~ (l1_pre_topc @ 
% 1.75/1.93             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.75/1.93      inference('sup+', [status(thm)], ['204', '205'])).
% 1.75/1.93  thf('207', plain,
% 1.75/1.93      (((u1_struct_0 @ 
% 1.75/1.93         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.75/1.93         = (u1_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['65', '66'])).
% 1.75/1.93  thf('208', plain,
% 1.75/1.93      ((l1_pre_topc @ 
% 1.75/1.93        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['9', '10'])).
% 1.75/1.93  thf('209', plain,
% 1.75/1.93      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.75/1.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['206', '207', '208'])).
% 1.75/1.93  thf('210', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('211', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('212', plain,
% 1.75/1.93      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 1.75/1.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))),
% 1.75/1.93      inference('demod', [status(thm)], ['209', '210', '211'])).
% 1.75/1.93  thf('213', plain,
% 1.75/1.93      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 1.75/1.93         = (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['120', '125', '202', '203', '212'])).
% 1.75/1.93  thf('214', plain,
% 1.75/1.93      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 1.75/1.93         != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.93  thf('215', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 1.75/1.93      inference('demod', [status(thm)], ['55', '56'])).
% 1.75/1.93  thf('216', plain,
% 1.75/1.93      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 1.75/1.93         != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['214', '215'])).
% 1.75/1.93  thf('217', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 1.75/1.93      inference('sup-', [status(thm)], ['72', '87'])).
% 1.75/1.93  thf('218', plain,
% 1.75/1.93      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 1.75/1.93         != (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.75/1.93      inference('demod', [status(thm)], ['216', '217'])).
% 1.75/1.93  thf('219', plain, ($false),
% 1.75/1.93      inference('simplify_reflect-', [status(thm)], ['213', '218'])).
% 1.75/1.93  
% 1.75/1.93  % SZS output end Refutation
% 1.75/1.93  
% 1.75/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
