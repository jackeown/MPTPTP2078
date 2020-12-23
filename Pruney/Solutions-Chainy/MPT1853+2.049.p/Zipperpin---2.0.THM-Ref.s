%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pKpxlw0Z0k

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 540 expanded)
%              Number of leaves         :   22 ( 156 expanded)
%              Depth                    :   25
%              Number of atoms          :  940 (7319 expanded)
%              Number of equality atoms :   15 (  60 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t20_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
          <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
            <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ X2 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('6',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d4_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_tex_2 @ A @ B ) )
              <=> ( ( u1_struct_0 @ C )
                  = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( X6
       != ( k1_tex_2 @ X5 @ X4 ) )
      | ( ( u1_struct_0 @ X6 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X5 ) @ X4 ) )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( v1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X5 @ X4 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X5 @ X4 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X5 @ X4 ) @ X5 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X5 @ X4 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X5 ) @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X7 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('17',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('26',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(t13_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ~ ( v1_tex_2 @ X9 @ X10 )
      | ( v1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_tex_2 @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('47',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ~ ( v1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( v1_tex_2 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_tex_2 @ X9 @ X10 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('63',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('69',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['44','67','68'])).

thf('70',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['42','69'])).

thf('71',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','70','71'])).

thf('73',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('74',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['44','67'])).

thf('75',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('80',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pKpxlw0Z0k
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 42 iterations in 0.028s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(t20_tex_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.49             ( v1_subset_1 @
% 0.21/0.49               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.49                ( v1_subset_1 @
% 0.21/0.49                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.49                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.21/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k6_domain_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X2)
% 0.21/0.49          | ~ (m1_subset_1 @ X3 @ X2)
% 0.21/0.49          | (m1_subset_1 @ (k6_domain_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k1_tex_2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.49         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.49         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X7)
% 0.21/0.49          | (v2_struct_0 @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.21/0.49          | (v1_pre_topc @ (k1_tex_2 @ X7 @ X8)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(d4_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.21/0.49                 ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.21/0.49                 ( ( u1_struct_0 @ C ) =
% 0.21/0.49                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.49          | ((X6) != (k1_tex_2 @ X5 @ X4))
% 0.21/0.49          | ((u1_struct_0 @ X6) = (k6_domain_1 @ (u1_struct_0 @ X5) @ X4))
% 0.21/0.49          | ~ (m1_pre_topc @ X6 @ X5)
% 0.21/0.49          | ~ (v1_pre_topc @ X6)
% 0.21/0.49          | (v2_struct_0 @ X6)
% 0.21/0.49          | ~ (l1_pre_topc @ X5)
% 0.21/0.49          | (v2_struct_0 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X5)
% 0.21/0.49          | ~ (l1_pre_topc @ X5)
% 0.21/0.49          | (v2_struct_0 @ (k1_tex_2 @ X5 @ X4))
% 0.21/0.49          | ~ (v1_pre_topc @ (k1_tex_2 @ X5 @ X4))
% 0.21/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ X5 @ X4) @ X5)
% 0.21/0.49          | ((u1_struct_0 @ (k1_tex_2 @ X5 @ X4))
% 0.21/0.49              = (k6_domain_1 @ (u1_struct_0 @ X5) @ X4))
% 0.21/0.49          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.49        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.49  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X7)
% 0.21/0.49          | (v2_struct_0 @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.21/0.49          | (m1_pre_topc @ (k1_tex_2 @ X7 @ X8) @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14', '21', '22'])).
% 0.21/0.49  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X7)
% 0.21/0.49          | (v2_struct_0 @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.21/0.49          | ~ (v2_struct_0 @ (k1_tex_2 @ X7 @ X8)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.49      inference('clc', [status(thm)], ['23', '30'])).
% 0.21/0.49  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf(t13_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                 ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) <=>
% 0.21/0.49                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.49          | ((X11) != (u1_struct_0 @ X9))
% 0.21/0.49          | ~ (v1_tex_2 @ X9 @ X10)
% 0.21/0.49          | (v1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.49          | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.49          | (v1_subset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10))
% 0.21/0.49          | ~ (v1_tex_2 @ X9 @ X10)
% 0.21/0.49          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.21/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.49             (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49             (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49           (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '38'])).
% 0.21/0.49  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49           (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A))) | 
% 0.21/0.49       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['41'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.49          | ((X11) != (u1_struct_0 @ X9))
% 0.21/0.49          | ~ (v1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.49          | (v1_tex_2 @ X9 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.49          | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.49          | (v1_tex_2 @ X9 @ X10)
% 0.21/0.49          | ~ (v1_subset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10))
% 0.21/0.49          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.21/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.49               (u1_struct_0 @ X0))
% 0.21/0.49          | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ X0))
% 0.21/0.49          | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49             (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '52'])).
% 0.21/0.49  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('55', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49             (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      ((((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['43'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.49  thf(fc2_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (![X1 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.21/0.49          | ~ (l1_struct_0 @ X1)
% 0.21/0.49          | (v2_struct_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_l1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.49  thf('63', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('demod', [status(thm)], ['61', '64'])).
% 0.21/0.49  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) | 
% 0.21/0.49       ~
% 0.21/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) | 
% 0.21/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['41'])).
% 0.21/0.49  thf('69', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['44', '67', '68'])).
% 0.21/0.49  thf('70', plain, ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['42', '69'])).
% 0.21/0.49  thf('71', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49           (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '40', '70', '71'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49           (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['43'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['44', '67'])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49          (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('76', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['72', '75'])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (![X1 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.21/0.49          | ~ (l1_struct_0 @ X1)
% 0.21/0.49          | (v2_struct_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('78', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.49  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('80', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.49  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
