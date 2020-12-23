%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oSkLwdn4rQ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:54 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  308 (3789 expanded)
%              Number of leaves         :   31 (1127 expanded)
%              Depth                    :   27
%              Number of atoms          : 2333 (43617 expanded)
%              Number of equality atoms :   98 (1558 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_tex_2 @ X23 @ X24 )
      | ( X25
       != ( u1_struct_0 @ X23 ) )
      | ( v1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_tex_2 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('26',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( v1_subset_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('32',plain,
    ( ( v1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( sk_C @ X23 @ X24 )
        = ( u1_struct_0 @ X23 ) )
      | ( v1_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('40',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('48',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X8
       != ( k1_pre_topc @ X7 @ X6 ) )
      | ( ( k2_struct_0 @ X8 )
        = X6 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('54',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('57',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('62',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('66',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','52','59','64','65'])).

thf('67',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['37','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('70',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('73',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('75',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('78',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('80',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','75','80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('84',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','82','83'])).

thf('85',plain,
    ( ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['35','36','84'])).

thf('86',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_subset_1 @ ( sk_C @ X23 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ( v1_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('89',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','94'])).

thf('96',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','95'])).

thf('97',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('99',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('100',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('104',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('105',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('109',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('110',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','107','112'])).

thf('114',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['97','113'])).

thf('115',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('118',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('121',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('125',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','125'])).

thf('127',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['115','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('129',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('131',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('133',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A )
    | ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','125'])).

thf('136',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('137',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('139',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('143',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('144',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('148',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134','141','146','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['123','124'])).

thf('150',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','148','149'])).

thf('151',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['96','150'])).

thf('152',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('153',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('154',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','94'])).

thf('156',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','94'])).

thf('157',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','148','149'])).

thf('159',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','148','149'])).

thf('160',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','82','83'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('163',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('165',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['161','167'])).

thf('169',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('170',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['168','169'])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('171',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('172',plain,
    ( ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','82','83'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('175',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['173','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('180',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','82','83'])).

thf('182',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('183',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['172','180','181','182'])).

thf('184',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('185',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','82','83'])).

thf('187',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['184','187'])).

thf('189',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['123','124'])).

thf('190',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['183','190'])).

thf('192',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('193',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['121','122'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['191','198'])).

thf('200',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('201',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['121','122'])).

thf('203',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','82','83'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('205',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('206',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('211',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['209','212'])).

thf('214',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['223','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['218','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['209','212'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['230','231'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('243',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['241','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('248',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['246','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['240','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['232','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['213','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('259',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('260',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['257','260'])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,
    ( ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['203','262'])).

thf('264',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','82','83'])).

thf('265',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('266',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['263','264','265'])).

thf('267',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','148','149'])).

thf('268',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['201','202','266','267'])).

thf('269',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['160','268'])).

thf('270',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['151','269'])).

thf('271',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_subset_1 @ X27 @ X26 )
      | ( X27 != X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('272',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_subset_1 @ X26 @ X26 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('274',plain,(
    ! [X26: $i] :
      ~ ( v1_subset_1 @ X26 @ X26 ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,(
    $false ),
    inference('sup-',[status(thm)],['270','274'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oSkLwdn4rQ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.86  % Solved by: fo/fo7.sh
% 0.67/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.86  % done 687 iterations in 0.394s
% 0.67/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.86  % SZS output start Refutation
% 0.67/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.86  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.67/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.67/0.86  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.67/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.86  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.67/0.86  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.67/0.86  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.67/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.86  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.67/0.86  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.67/0.86  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.67/0.86  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.67/0.86  thf(t14_tex_2, conjecture,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.86           ( ![C:$i]:
% 0.67/0.86             ( ( m1_pre_topc @ C @ A ) =>
% 0.67/0.86               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.67/0.86                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.67/0.86                   ( v1_tex_2 @ B @ A ) ) =>
% 0.67/0.86                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.67/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.86    (~( ![A:$i]:
% 0.67/0.86        ( ( l1_pre_topc @ A ) =>
% 0.67/0.86          ( ![B:$i]:
% 0.67/0.86            ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.86              ( ![C:$i]:
% 0.67/0.86                ( ( m1_pre_topc @ C @ A ) =>
% 0.67/0.86                  ( ( ( ( g1_pre_topc @
% 0.67/0.86                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.67/0.86                        ( g1_pre_topc @
% 0.67/0.86                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.67/0.86                      ( v1_tex_2 @ B @ A ) ) =>
% 0.67/0.86                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 0.67/0.86    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 0.67/0.86  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(t35_borsuk_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.86           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.67/0.86  thf('1', plain,
% 0.67/0.86      (![X21 : $i, X22 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X21 @ X22)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.67/0.86          | ~ (l1_pre_topc @ X22))),
% 0.67/0.86      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.67/0.86  thf('2', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['0', '1'])).
% 0.67/0.86  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('4', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.67/0.86  thf(t3_subset, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.86  thf('5', plain,
% 0.67/0.86      (![X3 : $i, X5 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('6', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.67/0.86  thf(d3_tex_2, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.86           ( ( v1_tex_2 @ B @ A ) <=>
% 0.67/0.86             ( ![C:$i]:
% 0.67/0.86               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.67/0.86                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.67/0.86  thf('7', plain,
% 0.67/0.86      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X23 @ X24)
% 0.67/0.86          | ~ (v1_tex_2 @ X23 @ X24)
% 0.67/0.86          | ((X25) != (u1_struct_0 @ X23))
% 0.67/0.86          | (v1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.67/0.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.67/0.86          | ~ (l1_pre_topc @ X24))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.67/0.86  thf('8', plain,
% 0.67/0.86      (![X23 : $i, X24 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X24)
% 0.67/0.86          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.67/0.86               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.67/0.86          | (v1_subset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 0.67/0.86          | ~ (v1_tex_2 @ X23 @ X24)
% 0.67/0.86          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.67/0.86      inference('simplify', [status(thm)], ['7'])).
% 0.67/0.86  thf('9', plain,
% 0.67/0.86      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.67/0.86        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.67/0.86        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['6', '8'])).
% 0.67/0.86  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('11', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('13', plain,
% 0.67/0.86      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.67/0.86  thf(d3_struct_0, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.67/0.86  thf('14', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('15', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('16', plain,
% 0.67/0.86      (![X21 : $i, X22 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X21 @ X22)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.67/0.86          | ~ (l1_pre_topc @ X22))),
% 0.67/0.86      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.67/0.86  thf('17', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['15', '16'])).
% 0.67/0.86  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('19', plain,
% 0.67/0.86      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.86  thf('20', plain,
% 0.67/0.86      (((r1_tarski @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('sup+', [status(thm)], ['14', '19'])).
% 0.67/0.86  thf('21', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(dt_m1_pre_topc, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.67/0.86  thf('22', plain,
% 0.67/0.86      (![X13 : $i, X14 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.67/0.86          | (l1_pre_topc @ X13)
% 0.67/0.86          | ~ (l1_pre_topc @ X14))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.86  thf('23', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['21', '22'])).
% 0.67/0.86  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('25', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['23', '24'])).
% 0.67/0.86  thf(dt_l1_pre_topc, axiom,
% 0.67/0.86    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.67/0.86  thf('26', plain,
% 0.67/0.86      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.86  thf('27', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.86      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.86  thf('28', plain,
% 0.67/0.86      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['20', '27'])).
% 0.67/0.86  thf('29', plain,
% 0.67/0.86      (![X3 : $i, X5 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('30', plain,
% 0.67/0.86      ((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.86  thf(d7_subset_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.86       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.67/0.86  thf('31', plain,
% 0.67/0.86      (![X26 : $i, X27 : $i]:
% 0.67/0.86         (((X27) = (X26))
% 0.67/0.86          | (v1_subset_1 @ X27 @ X26)
% 0.67/0.86          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.67/0.86      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.67/0.86  thf('32', plain,
% 0.67/0.86      (((v1_subset_1 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.86        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['30', '31'])).
% 0.67/0.86  thf('33', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('34', plain,
% 0.67/0.86      (![X23 : $i, X24 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X23 @ X24)
% 0.67/0.86          | ((sk_C @ X23 @ X24) = (u1_struct_0 @ X23))
% 0.67/0.86          | (v1_tex_2 @ X23 @ X24)
% 0.67/0.86          | ~ (l1_pre_topc @ X24))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.67/0.86  thf('35', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.67/0.86        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.86  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('37', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('38', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('39', plain,
% 0.67/0.86      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.86  thf('40', plain,
% 0.67/0.86      (((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_A))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup+', [status(thm)], ['38', '39'])).
% 0.67/0.86  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('42', plain,
% 0.67/0.86      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.86  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.86  thf('44', plain,
% 0.67/0.86      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['40', '43'])).
% 0.67/0.86  thf('45', plain,
% 0.67/0.86      (![X3 : $i, X5 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('46', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['44', '45'])).
% 0.67/0.86  thf('47', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf(d10_pre_topc, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86           ( ![C:$i]:
% 0.67/0.86             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.67/0.86               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.67/0.86                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.67/0.86  thf('48', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.67/0.86          | ((X8) != (k1_pre_topc @ X7 @ X6))
% 0.67/0.86          | ((k2_struct_0 @ X8) = (X6))
% 0.67/0.86          | ~ (m1_pre_topc @ X8 @ X7)
% 0.67/0.86          | ~ (v1_pre_topc @ X8)
% 0.67/0.86          | ~ (l1_pre_topc @ X7))),
% 0.67/0.86      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.67/0.86  thf('49', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X7)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.67/0.86          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.67/0.86      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.86  thf('50', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ X1) @ X0)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ X1))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['47', '49'])).
% 0.67/0.86  thf('51', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.86        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)) @ sk_A)
% 0.67/0.86        | ((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.86            = (u1_struct_0 @ sk_C_1))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['46', '50'])).
% 0.67/0.86  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('53', plain,
% 0.67/0.86      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.86  thf('54', plain,
% 0.67/0.86      (![X3 : $i, X5 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('55', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['53', '54'])).
% 0.67/0.86  thf(dt_k1_pre_topc, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( l1_pre_topc @ A ) & 
% 0.67/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.86       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.67/0.86         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.67/0.86  thf('56', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X10)
% 0.67/0.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.86          | (v1_pre_topc @ (k1_pre_topc @ X10 @ X11)))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.86  thf('57', plain,
% 0.67/0.86      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['55', '56'])).
% 0.67/0.86  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('59', plain,
% 0.67/0.86      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '58'])).
% 0.67/0.86  thf('60', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['53', '54'])).
% 0.67/0.86  thf('61', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X10)
% 0.67/0.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.86          | (m1_pre_topc @ (k1_pre_topc @ X10 @ X11) @ X10))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.86  thf('62', plain,
% 0.67/0.86      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)) @ sk_A)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['60', '61'])).
% 0.67/0.86  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('64', plain,
% 0.67/0.86      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)) @ sk_A)),
% 0.67/0.86      inference('demod', [status(thm)], ['62', '63'])).
% 0.67/0.86  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.86  thf('66', plain,
% 0.67/0.86      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.86         = (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['51', '52', '59', '64', '65'])).
% 0.67/0.86  thf('67', plain,
% 0.67/0.86      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.86          = (u1_struct_0 @ sk_C_1))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('sup+', [status(thm)], ['37', '66'])).
% 0.67/0.86  thf('68', plain,
% 0.67/0.86      ((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.86  thf('69', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X7)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.67/0.86          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.67/0.86      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.86  thf('70', plain,
% 0.67/0.86      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.86          = (k2_struct_0 @ sk_C_1))
% 0.67/0.86        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)
% 0.67/0.86        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['68', '69'])).
% 0.67/0.86  thf('71', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('72', plain,
% 0.67/0.86      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)) @ sk_A)),
% 0.67/0.86      inference('demod', [status(thm)], ['62', '63'])).
% 0.67/0.86  thf('73', plain,
% 0.67/0.86      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)
% 0.67/0.86        | ~ (l1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('sup+', [status(thm)], ['71', '72'])).
% 0.67/0.86  thf('74', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.86      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.86  thf('75', plain,
% 0.67/0.86      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)),
% 0.67/0.86      inference('demod', [status(thm)], ['73', '74'])).
% 0.67/0.86  thf('76', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('77', plain,
% 0.67/0.86      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '58'])).
% 0.67/0.86  thf('78', plain,
% 0.67/0.86      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('sup+', [status(thm)], ['76', '77'])).
% 0.67/0.86  thf('79', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.86      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.86  thf('80', plain,
% 0.67/0.86      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['78', '79'])).
% 0.67/0.86  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('82', plain,
% 0.67/0.86      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.86         = (k2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['70', '75', '80', '81'])).
% 0.67/0.86  thf('83', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.86      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.86  thf('84', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['67', '82', '83'])).
% 0.67/0.86  thf('85', plain,
% 0.67/0.86      (((v1_tex_2 @ sk_C_1 @ sk_A)
% 0.67/0.86        | ((sk_C @ sk_C_1 @ sk_A) = (k2_struct_0 @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['35', '36', '84'])).
% 0.67/0.86  thf('86', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('87', plain, (((sk_C @ sk_C_1 @ sk_A) = (k2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('clc', [status(thm)], ['85', '86'])).
% 0.67/0.86  thf('88', plain,
% 0.67/0.86      (![X23 : $i, X24 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X23 @ X24)
% 0.67/0.86          | ~ (v1_subset_1 @ (sk_C @ X23 @ X24) @ (u1_struct_0 @ X24))
% 0.67/0.86          | (v1_tex_2 @ X23 @ X24)
% 0.67/0.86          | ~ (l1_pre_topc @ X24))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.67/0.86  thf('89', plain,
% 0.67/0.86      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.67/0.86        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['87', '88'])).
% 0.67/0.86  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('91', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('92', plain,
% 0.67/0.86      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.86        | (v1_tex_2 @ sk_C_1 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.67/0.86  thf('93', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('94', plain,
% 0.67/0.86      (~ (v1_subset_1 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('clc', [status(thm)], ['92', '93'])).
% 0.67/0.86  thf('95', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('clc', [status(thm)], ['32', '94'])).
% 0.67/0.86  thf('96', plain,
% 0.67/0.86      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['13', '95'])).
% 0.67/0.86  thf('97', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('98', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.67/0.86  thf('99', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X7)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.67/0.86          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.67/0.86      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.86  thf('100', plain,
% 0.67/0.86      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.86          = (u1_struct_0 @ sk_B))
% 0.67/0.86        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)
% 0.67/0.86        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['98', '99'])).
% 0.67/0.86  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('102', plain,
% 0.67/0.86      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.86          = (u1_struct_0 @ sk_B))
% 0.67/0.86        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)
% 0.67/0.86        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('demod', [status(thm)], ['100', '101'])).
% 0.67/0.86  thf('103', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.67/0.86  thf('104', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X10)
% 0.67/0.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.86          | (m1_pre_topc @ (k1_pre_topc @ X10 @ X11) @ X10))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.86  thf('105', plain,
% 0.67/0.86      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['103', '104'])).
% 0.67/0.86  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('107', plain,
% 0.67/0.86      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)),
% 0.67/0.86      inference('demod', [status(thm)], ['105', '106'])).
% 0.67/0.86  thf('108', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.67/0.86  thf('109', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X10)
% 0.67/0.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.86          | (v1_pre_topc @ (k1_pre_topc @ X10 @ X11)))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.86  thf('110', plain,
% 0.67/0.86      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['108', '109'])).
% 0.67/0.86  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('112', plain,
% 0.67/0.86      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['110', '111'])).
% 0.67/0.86  thf('113', plain,
% 0.67/0.86      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.86         = (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['102', '107', '112'])).
% 0.67/0.86  thf('114', plain,
% 0.67/0.86      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.86          = (u1_struct_0 @ sk_B))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup+', [status(thm)], ['97', '113'])).
% 0.67/0.86  thf('115', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('116', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('117', plain,
% 0.67/0.86      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.67/0.86  thf('118', plain,
% 0.67/0.86      (((r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup+', [status(thm)], ['116', '117'])).
% 0.67/0.86  thf('119', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('120', plain,
% 0.67/0.86      (![X13 : $i, X14 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.67/0.86          | (l1_pre_topc @ X13)
% 0.67/0.86          | ~ (l1_pre_topc @ X14))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.86  thf('121', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['119', '120'])).
% 0.67/0.86  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('123', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.86      inference('demod', [status(thm)], ['121', '122'])).
% 0.67/0.86  thf('124', plain,
% 0.67/0.86      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.86  thf('125', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.86      inference('sup-', [status(thm)], ['123', '124'])).
% 0.67/0.86  thf('126', plain,
% 0.67/0.86      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['118', '125'])).
% 0.67/0.86  thf('127', plain,
% 0.67/0.86      (((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup+', [status(thm)], ['115', '126'])).
% 0.67/0.86  thf('128', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.86  thf('129', plain,
% 0.67/0.86      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['127', '128'])).
% 0.67/0.86  thf('130', plain,
% 0.67/0.86      (![X3 : $i, X5 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('131', plain,
% 0.67/0.86      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['129', '130'])).
% 0.67/0.86  thf('132', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ X1) @ X0)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ X1))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['47', '49'])).
% 0.67/0.86  thf('133', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.86        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A)
% 0.67/0.86        | ((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.86            = (k2_struct_0 @ sk_B))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['131', '132'])).
% 0.67/0.86  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('135', plain,
% 0.67/0.86      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['118', '125'])).
% 0.67/0.86  thf('136', plain,
% 0.67/0.86      (![X3 : $i, X5 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('137', plain,
% 0.67/0.86      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['135', '136'])).
% 0.67/0.86  thf('138', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X10)
% 0.67/0.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.86          | (v1_pre_topc @ (k1_pre_topc @ X10 @ X11)))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.86  thf('139', plain,
% 0.67/0.86      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['137', '138'])).
% 0.67/0.86  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('141', plain,
% 0.67/0.86      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['139', '140'])).
% 0.67/0.86  thf('142', plain,
% 0.67/0.86      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['135', '136'])).
% 0.67/0.86  thf('143', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X10)
% 0.67/0.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.86          | (m1_pre_topc @ (k1_pre_topc @ X10 @ X11) @ X10))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.86  thf('144', plain,
% 0.67/0.86      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['142', '143'])).
% 0.67/0.86  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('146', plain,
% 0.67/0.86      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A)),
% 0.67/0.86      inference('demod', [status(thm)], ['144', '145'])).
% 0.67/0.86  thf('147', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.86  thf('148', plain,
% 0.67/0.86      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.86         = (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['133', '134', '141', '146', '147'])).
% 0.67/0.86  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.86      inference('sup-', [status(thm)], ['123', '124'])).
% 0.67/0.86  thf('150', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['114', '148', '149'])).
% 0.67/0.86  thf('151', plain,
% 0.67/0.86      ((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['96', '150'])).
% 0.67/0.86  thf('152', plain,
% 0.67/0.86      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.67/0.86  thf(d10_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.86  thf('153', plain,
% 0.67/0.86      (![X0 : $i, X2 : $i]:
% 0.67/0.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.86  thf('154', plain,
% 0.67/0.86      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.86        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['152', '153'])).
% 0.67/0.86  thf('155', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('clc', [status(thm)], ['32', '94'])).
% 0.67/0.86  thf('156', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('clc', [status(thm)], ['32', '94'])).
% 0.67/0.86  thf('157', plain,
% 0.67/0.86      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))
% 0.67/0.86        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.67/0.86  thf('158', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['114', '148', '149'])).
% 0.67/0.86  thf('159', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['114', '148', '149'])).
% 0.67/0.86  thf('160', plain,
% 0.67/0.86      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 0.67/0.86        | ((k2_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.67/0.86  thf('161', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['67', '82', '83'])).
% 0.67/0.86  thf('162', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.67/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.86  thf('163', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.67/0.86      inference('simplify', [status(thm)], ['162'])).
% 0.67/0.86  thf('164', plain,
% 0.67/0.86      (![X3 : $i, X5 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('165', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['163', '164'])).
% 0.67/0.86  thf('166', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X10)
% 0.67/0.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.86          | (m1_pre_topc @ (k1_pre_topc @ X10 @ X11) @ X10))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.86  thf('167', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['165', '166'])).
% 0.67/0.86  thf('168', plain,
% 0.67/0.86      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)) @ sk_C_1)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_C_1))),
% 0.67/0.86      inference('sup+', [status(thm)], ['161', '167'])).
% 0.67/0.86  thf('169', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['23', '24'])).
% 0.67/0.86  thf('170', plain,
% 0.67/0.86      ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)) @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['168', '169'])).
% 0.67/0.86  thf(t65_pre_topc, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( l1_pre_topc @ B ) =>
% 0.67/0.86           ( ( m1_pre_topc @ A @ B ) <=>
% 0.67/0.86             ( m1_pre_topc @
% 0.67/0.86               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.67/0.86  thf('171', plain,
% 0.67/0.86      (![X17 : $i, X18 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X17)
% 0.67/0.86          | ~ (m1_pre_topc @ X18 @ X17)
% 0.67/0.86          | (m1_pre_topc @ X18 @ 
% 0.67/0.86             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.67/0.86          | ~ (l1_pre_topc @ X18))),
% 0.67/0.86      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.67/0.86  thf('172', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.86        | (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)) @ 
% 0.67/0.86           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_C_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['170', '171'])).
% 0.67/0.86  thf('173', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['67', '82', '83'])).
% 0.67/0.86  thf('174', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['165', '166'])).
% 0.67/0.86  thf('175', plain,
% 0.67/0.86      (![X13 : $i, X14 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.67/0.86          | (l1_pre_topc @ X13)
% 0.67/0.86          | ~ (l1_pre_topc @ X14))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.86  thf('176', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['174', '175'])).
% 0.67/0.86  thf('177', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['176'])).
% 0.67/0.86  thf('178', plain,
% 0.67/0.86      (((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_C_1))),
% 0.67/0.86      inference('sup+', [status(thm)], ['173', '177'])).
% 0.67/0.86  thf('179', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['23', '24'])).
% 0.67/0.86  thf('180', plain,
% 0.67/0.86      ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['178', '179'])).
% 0.67/0.86  thf('181', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['67', '82', '83'])).
% 0.67/0.86  thf('182', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['23', '24'])).
% 0.67/0.86  thf('183', plain,
% 0.67/0.86      ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)) @ 
% 0.67/0.86        (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['172', '180', '181', '182'])).
% 0.67/0.86  thf('184', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('185', plain,
% 0.67/0.86      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.86         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('186', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['67', '82', '83'])).
% 0.67/0.86  thf('187', plain,
% 0.67/0.86      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.86         = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['185', '186'])).
% 0.67/0.86  thf('188', plain,
% 0.67/0.86      ((((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.86          = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup+', [status(thm)], ['184', '187'])).
% 0.67/0.86  thf('189', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.86      inference('sup-', [status(thm)], ['123', '124'])).
% 0.67/0.86  thf('190', plain,
% 0.67/0.86      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.86         = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['188', '189'])).
% 0.67/0.86  thf('191', plain,
% 0.67/0.86      ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)) @ 
% 0.67/0.86        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['183', '190'])).
% 0.67/0.86  thf('192', plain,
% 0.67/0.86      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.86         = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['185', '186'])).
% 0.67/0.86  thf(t59_pre_topc, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_pre_topc @
% 0.67/0.86             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.67/0.86           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.67/0.86  thf('193', plain,
% 0.67/0.86      (![X15 : $i, X16 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X15 @ 
% 0.67/0.86             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.67/0.86          | (m1_pre_topc @ X15 @ X16)
% 0.67/0.86          | ~ (l1_pre_topc @ X16))),
% 0.67/0.86      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.67/0.86  thf('194', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X0 @ 
% 0.67/0.86             (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.67/0.86          | (m1_pre_topc @ X0 @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['192', '193'])).
% 0.67/0.86  thf('195', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.86      inference('demod', [status(thm)], ['121', '122'])).
% 0.67/0.86  thf('196', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X0 @ 
% 0.67/0.86             (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.86          | (m1_pre_topc @ X0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['194', '195'])).
% 0.67/0.86  thf('197', plain,
% 0.67/0.86      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.86         = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['188', '189'])).
% 0.67/0.86  thf('198', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X0 @ 
% 0.67/0.86             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.67/0.86          | (m1_pre_topc @ X0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['196', '197'])).
% 0.67/0.86  thf('199', plain,
% 0.67/0.86      ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)) @ sk_B)),
% 0.67/0.86      inference('sup-', [status(thm)], ['191', '198'])).
% 0.67/0.86  thf('200', plain,
% 0.67/0.86      (![X21 : $i, X22 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X21 @ X22)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.67/0.86          | ~ (l1_pre_topc @ X22))),
% 0.67/0.86      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.67/0.86  thf('201', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ sk_B)
% 0.67/0.86        | (r1_tarski @ 
% 0.67/0.86           (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1))) @ 
% 0.67/0.86           (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['199', '200'])).
% 0.67/0.86  thf('202', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.86      inference('demod', [status(thm)], ['121', '122'])).
% 0.67/0.86  thf('203', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['67', '82', '83'])).
% 0.67/0.86  thf('204', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['165', '166'])).
% 0.67/0.86  thf('205', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['163', '164'])).
% 0.67/0.86  thf('206', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X7)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.67/0.86          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.67/0.86      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.86  thf('207', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86            = (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['205', '206'])).
% 0.67/0.86  thf('208', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86              = (u1_struct_0 @ X0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['204', '207'])).
% 0.67/0.86  thf('209', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86            = (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['208'])).
% 0.67/0.86  thf('210', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['163', '164'])).
% 0.67/0.86  thf('211', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X10)
% 0.67/0.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.86          | (v1_pre_topc @ (k1_pre_topc @ X10 @ X11)))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.86  thf('212', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['210', '211'])).
% 0.67/0.86  thf('213', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86              = (u1_struct_0 @ X0)))),
% 0.67/0.86      inference('clc', [status(thm)], ['209', '212'])).
% 0.67/0.86  thf('214', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('215', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['165', '166'])).
% 0.67/0.86  thf('216', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['214', '215'])).
% 0.67/0.86  thf('217', plain,
% 0.67/0.86      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.86  thf('218', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0))),
% 0.67/0.86      inference('clc', [status(thm)], ['216', '217'])).
% 0.67/0.86  thf('219', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('220', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['210', '211'])).
% 0.67/0.86  thf('221', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['219', '220'])).
% 0.67/0.86  thf('222', plain,
% 0.67/0.86      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.86  thf('223', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | (v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.67/0.86      inference('clc', [status(thm)], ['221', '222'])).
% 0.67/0.86  thf('224', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['163', '164'])).
% 0.67/0.86  thf('225', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ X1) @ X0)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ X1))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['47', '49'])).
% 0.67/0.86  thf('226', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86              = (k2_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_struct_0 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['224', '225'])).
% 0.67/0.86  thf('227', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86              = (k2_struct_0 @ X0))
% 0.67/0.86          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['223', '226'])).
% 0.67/0.86  thf('228', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86              = (k2_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['227'])).
% 0.67/0.86  thf('229', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86              = (k2_struct_0 @ X0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['218', '228'])).
% 0.67/0.86  thf('230', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86            = (k2_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['229'])).
% 0.67/0.86  thf('231', plain,
% 0.67/0.86      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.86  thf('232', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86              = (k2_struct_0 @ X0)))),
% 0.67/0.86      inference('clc', [status(thm)], ['230', '231'])).
% 0.67/0.86  thf('233', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('234', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86              = (u1_struct_0 @ X0)))),
% 0.67/0.86      inference('clc', [status(thm)], ['209', '212'])).
% 0.67/0.86  thf('235', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86            = (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['233', '234'])).
% 0.67/0.86  thf('236', plain,
% 0.67/0.86      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.86  thf('237', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86              = (u1_struct_0 @ X0)))),
% 0.67/0.86      inference('clc', [status(thm)], ['235', '236'])).
% 0.67/0.86  thf('238', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.86              = (k2_struct_0 @ X0)))),
% 0.67/0.86      inference('clc', [status(thm)], ['230', '231'])).
% 0.67/0.86  thf('239', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['237', '238'])).
% 0.67/0.86  thf('240', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['239'])).
% 0.67/0.86  thf('241', plain,
% 0.67/0.86      (![X9 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('242', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['165', '166'])).
% 0.67/0.86  thf('243', plain,
% 0.67/0.86      (![X21 : $i, X22 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X21 @ X22)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.67/0.86          | ~ (l1_pre_topc @ X22))),
% 0.67/0.86      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.67/0.86  thf('244', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | (r1_tarski @ 
% 0.67/0.86             (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 0.67/0.86             (u1_struct_0 @ X0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['242', '243'])).
% 0.67/0.86  thf('245', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((r1_tarski @ 
% 0.67/0.86           (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 0.67/0.86           (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['244'])).
% 0.67/0.86  thf('246', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((r1_tarski @ 
% 0.67/0.86           (k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 0.67/0.86           (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['241', '245'])).
% 0.67/0.86  thf('247', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['176'])).
% 0.67/0.86  thf('248', plain,
% 0.67/0.86      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.86  thf('249', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | (l1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['247', '248'])).
% 0.67/0.86  thf('250', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | (r1_tarski @ 
% 0.67/0.86             (k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 0.67/0.86             (u1_struct_0 @ X0)))),
% 0.67/0.86      inference('clc', [status(thm)], ['246', '249'])).
% 0.67/0.86  thf('251', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((r1_tarski @ 
% 0.67/0.86           (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.67/0.86           (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['240', '250'])).
% 0.67/0.86  thf('252', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | (r1_tarski @ 
% 0.67/0.86             (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.67/0.86             (u1_struct_0 @ X0)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['251'])).
% 0.67/0.86  thf('253', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['232', '252'])).
% 0.67/0.86  thf('254', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['253'])).
% 0.67/0.86  thf('255', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.67/0.86           (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.67/0.86      inference('sup+', [status(thm)], ['213', '254'])).
% 0.67/0.86  thf('256', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['176'])).
% 0.67/0.86  thf('257', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.67/0.86             (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 0.67/0.86      inference('clc', [status(thm)], ['255', '256'])).
% 0.67/0.86  thf('258', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((r1_tarski @ 
% 0.67/0.86           (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 0.67/0.86           (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['244'])).
% 0.67/0.86  thf('259', plain,
% 0.67/0.86      (![X0 : $i, X2 : $i]:
% 0.67/0.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.86  thf('260', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.67/0.86               (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 0.67/0.86          | ((u1_struct_0 @ X0)
% 0.67/0.86              = (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['258', '259'])).
% 0.67/0.86  thf('261', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X0)
% 0.67/0.86          | ((u1_struct_0 @ X0)
% 0.67/0.86              = (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['257', '260'])).
% 0.67/0.86  thf('262', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (((u1_struct_0 @ X0)
% 0.67/0.86            = (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['261'])).
% 0.67/0.86  thf('263', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_C_1)
% 0.67/0.86          = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1))))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_C_1))),
% 0.67/0.86      inference('sup+', [status(thm)], ['203', '262'])).
% 0.67/0.86  thf('264', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['67', '82', '83'])).
% 0.67/0.86  thf('265', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['23', '24'])).
% 0.67/0.86  thf('266', plain,
% 0.67/0.86      (((k2_struct_0 @ sk_C_1)
% 0.67/0.86         = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1))))),
% 0.67/0.86      inference('demod', [status(thm)], ['263', '264', '265'])).
% 0.67/0.86  thf('267', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['114', '148', '149'])).
% 0.67/0.86  thf('268', plain,
% 0.67/0.86      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['201', '202', '266', '267'])).
% 0.67/0.86  thf('269', plain, (((k2_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['160', '268'])).
% 0.67/0.86  thf('270', plain,
% 0.67/0.86      ((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['151', '269'])).
% 0.67/0.86  thf('271', plain,
% 0.67/0.86      (![X26 : $i, X27 : $i]:
% 0.67/0.86         (~ (v1_subset_1 @ X27 @ X26)
% 0.67/0.86          | ((X27) != (X26))
% 0.67/0.86          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.67/0.86      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.67/0.86  thf('272', plain,
% 0.67/0.86      (![X26 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))
% 0.67/0.86          | ~ (v1_subset_1 @ X26 @ X26))),
% 0.67/0.86      inference('simplify', [status(thm)], ['271'])).
% 0.67/0.86  thf('273', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['163', '164'])).
% 0.67/0.86  thf('274', plain, (![X26 : $i]: ~ (v1_subset_1 @ X26 @ X26)),
% 0.67/0.86      inference('demod', [status(thm)], ['272', '273'])).
% 0.67/0.86  thf('275', plain, ($false), inference('sup-', [status(thm)], ['270', '274'])).
% 0.67/0.86  
% 0.67/0.86  % SZS output end Refutation
% 0.67/0.86  
% 0.67/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
