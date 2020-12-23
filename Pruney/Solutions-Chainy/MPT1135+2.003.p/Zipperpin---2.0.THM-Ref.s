%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j68rAgA4Gq

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 230 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  684 (4119 expanded)
%              Number of equality atoms :   30 ( 210 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t66_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) )
             => ( ( B = C )
               => ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ A @ B ) ) )
                  = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) )
               => ( ( B = C )
                 => ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ A @ B ) ) )
                    = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_pre_topc])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_B = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( X3
       != ( k1_pre_topc @ X2 @ X1 ) )
      | ( ( k2_struct_0 @ X3 )
        = X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( v1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X2 @ X1 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X2 @ X1 ) @ X2 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('14',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('20',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( ( k2_struct_0 @ X3 )
       != X1 )
      | ( X3
        = ( k1_pre_topc @ X2 @ X1 ) )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( v1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( X3
        = ( k1_pre_topc @ X2 @ ( k2_struct_0 @ X3 ) ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k1_pre_topc @ sk_A @ sk_C )
        = ( k1_pre_topc @ X0 @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['17','22'])).

thf('28',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k1_pre_topc @ sk_A @ sk_C )
        = ( k1_pre_topc @ X0 @ sk_C ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( k1_pre_topc @ sk_A @ sk_C )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','29'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('32',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
 != ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_B = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ) )
 != ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_C )
     != ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('38',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_C )
     != ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k1_pre_topc @ sk_A @ sk_C )
 != ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','44'])).

thf('46',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) )
    | ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','51'])).

thf('53',plain,(
    ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j68rAgA4Gq
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 44 iterations in 0.026s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.48  thf(dt_u1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( u1_pre_topc @ A ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X10 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.48          | ~ (l1_pre_topc @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.48  thf(dt_g1_pre_topc, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.48       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.20/0.48         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         ((l1_pre_topc @ (g1_pre_topc @ X4 @ X5))
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | (l1_pre_topc @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t66_pre_topc, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @
% 0.20/0.48                 C @ 
% 0.20/0.48                 ( k1_zfmisc_1 @
% 0.20/0.48                   ( u1_struct_0 @
% 0.20/0.48                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) =>
% 0.20/0.48               ( ( ( B ) = ( C ) ) =>
% 0.20/0.48                 ( ( g1_pre_topc @
% 0.20/0.48                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.20/0.48                     ( u1_pre_topc @ ( k1_pre_topc @ A @ B ) ) ) =
% 0.20/0.48                   ( k1_pre_topc @
% 0.20/0.48                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.20/0.48                     C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_pre_topc @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_subset_1 @
% 0.20/0.48                    C @ 
% 0.20/0.48                    ( k1_zfmisc_1 @
% 0.20/0.48                      ( u1_struct_0 @
% 0.20/0.48                        ( g1_pre_topc @
% 0.20/0.48                          ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) =>
% 0.20/0.48                  ( ( ( B ) = ( C ) ) =>
% 0.20/0.48                    ( ( g1_pre_topc @
% 0.20/0.48                        ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.20/0.48                        ( u1_pre_topc @ ( k1_pre_topc @ A @ B ) ) ) =
% 0.20/0.48                      ( k1_pre_topc @
% 0.20/0.48                        ( g1_pre_topc @
% 0.20/0.48                          ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.20/0.48                        C ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t66_pre_topc])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (u1_struct_0 @ 
% 0.20/0.48          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain, (((sk_B) = (sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(d10_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.48               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.20/0.48                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.48          | ((X3) != (k1_pre_topc @ X2 @ X1))
% 0.20/0.48          | ((k2_struct_0 @ X3) = (X1))
% 0.20/0.48          | ~ (m1_pre_topc @ X3 @ X2)
% 0.20/0.48          | ~ (v1_pre_topc @ X3)
% 0.20/0.48          | ~ (l1_pre_topc @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X2)
% 0.20/0.48          | ~ (v1_pre_topc @ (k1_pre_topc @ X2 @ X1))
% 0.20/0.48          | ~ (m1_pre_topc @ (k1_pre_topc @ X2 @ X1) @ X2)
% 0.20/0.48          | ((k2_struct_0 @ (k1_pre_topc @ X2 @ X1)) = (X1))
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))
% 0.20/0.48        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)
% 0.20/0.48        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.48  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))
% 0.20/0.48        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)
% 0.20/0.48        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(dt_k1_pre_topc, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.20/0.48         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X6)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.48          | (v1_pre_topc @ (k1_pre_topc @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C)) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))
% 0.20/0.48        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X6)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.48          | (m1_pre_topc @ (k1_pre_topc @ X6 @ X7) @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.48          | ((k2_struct_0 @ X3) != (X1))
% 0.20/0.48          | ((X3) = (k1_pre_topc @ X2 @ X1))
% 0.20/0.48          | ~ (m1_pre_topc @ X3 @ X2)
% 0.20/0.48          | ~ (v1_pre_topc @ X3)
% 0.20/0.48          | ~ (l1_pre_topc @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X2)
% 0.20/0.48          | ~ (v1_pre_topc @ X3)
% 0.20/0.48          | ~ (m1_pre_topc @ X3 @ X2)
% 0.20/0.48          | ((X3) = (k1_pre_topc @ X2 @ (k2_struct_0 @ X3)))
% 0.20/0.48          | ~ (m1_subset_1 @ (k2_struct_0 @ X3) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X2))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ((k1_pre_topc @ sk_A @ sk_C)
% 0.20/0.48              = (k1_pre_topc @ X0 @ (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_C))))
% 0.20/0.48          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ X0)
% 0.20/0.48          | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.48  thf('27', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.48  thf('28', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ((k1_pre_topc @ sk_A @ sk_C) = (k1_pre_topc @ X0 @ sk_C))
% 0.20/0.48          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ 
% 0.20/0.48           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.48        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.48        | ((k1_pre_topc @ sk_A @ sk_C)
% 0.20/0.48            = (k1_pre_topc @ 
% 0.20/0.48               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.48               sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '29'])).
% 0.20/0.48  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ( v1_pre_topc @ A ) =>
% 0.20/0.48         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_pre_topc @ X0)
% 0.20/0.48          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.48         (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.20/0.48         != (k1_pre_topc @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain, (((sk_B) = (sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, (((sk_B) = (sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) @ 
% 0.20/0.48         (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C)))
% 0.20/0.48         != (k1_pre_topc @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((((k1_pre_topc @ sk_A @ sk_C)
% 0.20/0.48          != (k1_pre_topc @ 
% 0.20/0.48              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.48              sk_C))
% 0.20/0.48        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C))
% 0.20/0.48        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '35'])).
% 0.20/0.48  thf('37', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((((k1_pre_topc @ sk_A @ sk_C)
% 0.20/0.48          != (k1_pre_topc @ 
% 0.20/0.48              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.48              sk_C))
% 0.20/0.48        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf(dt_m1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (((k1_pre_topc @ sk_A @ sk_C)
% 0.20/0.48         != (k1_pre_topc @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['38', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ 
% 0.20/0.48           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.48        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['30', '44'])).
% 0.20/0.48  thf('46', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf(t65_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( l1_pre_topc @ B ) =>
% 0.20/0.48           ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.48             ( m1_pre_topc @
% 0.20/0.48               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (m1_pre_topc @ X12 @ X11)
% 0.20/0.48          | (m1_pre_topc @ X12 @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.20/0.48          | ~ (l1_pre_topc @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C))
% 0.20/0.48        | (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ 
% 0.20/0.48           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ 
% 0.20/0.48        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (~ (l1_pre_topc @ 
% 0.20/0.48          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['45', '51'])).
% 0.20/0.48  thf('53', plain, (~ (l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '52'])).
% 0.20/0.48  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('55', plain, ($false), inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
