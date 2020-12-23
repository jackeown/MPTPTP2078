%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vLdqSnZr9S

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 433 expanded)
%              Number of leaves         :   23 ( 127 expanded)
%              Depth                    :   20
%              Number of atoms          :  875 (5835 expanded)
%              Number of equality atoms :   17 (  50 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X10 @ X11 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( X9
       != ( k1_tex_2 @ X8 @ X7 ) )
      | ( ( u1_struct_0 @ X9 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X8 ) @ X7 ) )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( v1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X8 @ X7 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X8 @ X7 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X8 @ X7 ) @ X8 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X8 @ X7 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X8 ) @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X10 @ X11 ) @ X10 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X10 @ X11 ) ) ) ),
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

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( v1_tex_2 @ X4 @ X5 )
      | ( X6
       != ( u1_struct_0 @ X4 ) )
      | ( v1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_tex_2 @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X4 @ X5 ) ) ),
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
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('47',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( ( sk_C @ X4 @ X5 )
        = ( u1_struct_0 @ X4 ) )
      | ( v1_tex_2 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('53',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( v1_subset_1 @ ( sk_C @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( v1_tex_2 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('55',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('58',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('60',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','60'])).

thf('62',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','61'])).

thf('63',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('64',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['44','62','63'])).

thf('65',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['42','64'])).

thf('66',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','65','66'])).

thf('68',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('69',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['44','62'])).

thf('70',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['67','70'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('72',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('75',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vLdqSnZr9S
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:31:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 52 iterations in 0.031s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.20/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(t20_tex_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.48             ( v1_subset_1 @
% 0.20/0.48               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.48                ( v1_subset_1 @
% 0.20/0.48                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.48                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.20/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k6_domain_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X2)
% 0.20/0.48          | ~ (m1_subset_1 @ X3 @ X2)
% 0.20/0.48          | (m1_subset_1 @ (k6_domain_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k1_tex_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.48         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.48         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X10)
% 0.20/0.48          | (v2_struct_0 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.20/0.48          | (v1_pre_topc @ (k1_tex_2 @ X10 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(d4_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.48                 ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.48               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.20/0.48                 ( ( u1_struct_0 @ C ) =
% 0.20/0.48                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ((X9) != (k1_tex_2 @ X8 @ X7))
% 0.20/0.48          | ((u1_struct_0 @ X9) = (k6_domain_1 @ (u1_struct_0 @ X8) @ X7))
% 0.20/0.48          | ~ (m1_pre_topc @ X9 @ X8)
% 0.20/0.48          | ~ (v1_pre_topc @ X9)
% 0.20/0.48          | (v2_struct_0 @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ X8)
% 0.20/0.48          | (v2_struct_0 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X8)
% 0.20/0.48          | ~ (l1_pre_topc @ X8)
% 0.20/0.48          | (v2_struct_0 @ (k1_tex_2 @ X8 @ X7))
% 0.20/0.48          | ~ (v1_pre_topc @ (k1_tex_2 @ X8 @ X7))
% 0.20/0.48          | ~ (m1_pre_topc @ (k1_tex_2 @ X8 @ X7) @ X8)
% 0.20/0.48          | ((u1_struct_0 @ (k1_tex_2 @ X8 @ X7))
% 0.20/0.48              = (k6_domain_1 @ (u1_struct_0 @ X8) @ X7))
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.48  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X10)
% 0.20/0.48          | (v2_struct_0 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.20/0.48          | (m1_pre_topc @ (k1_tex_2 @ X10 @ X11) @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14', '21', '22'])).
% 0.20/0.48  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X10)
% 0.20/0.48          | (v2_struct_0 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.20/0.48          | ~ (v2_struct_0 @ (k1_tex_2 @ X10 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['23', '30'])).
% 0.20/0.48  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf(d3_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( ( v1_tex_2 @ B @ A ) <=>
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X4 @ X5)
% 0.20/0.48          | ~ (v1_tex_2 @ X4 @ X5)
% 0.20/0.48          | ((X6) != (u1_struct_0 @ X4))
% 0.20/0.48          | (v1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X5)
% 0.20/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X4) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.48          | (v1_subset_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X5))
% 0.20/0.48          | ~ (v1_tex_2 @ X4 @ X5)
% 0.20/0.48          | ~ (m1_pre_topc @ X4 @ X5))),
% 0.20/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.20/0.48          | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.20/0.48          | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.20/0.48             (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.20/0.48          | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.20/0.48          | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48             (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A))
% 0.20/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '38'])).
% 0.20/0.48  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A))
% 0.20/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A))) | 
% 0.20/0.48       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['41'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.48         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('47', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X4 @ X5)
% 0.20/0.48          | ((sk_C @ X4 @ X5) = (u1_struct_0 @ X4))
% 0.20/0.48          | (v1_tex_2 @ X4 @ X5)
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['43'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X4 @ X5)
% 0.20/0.48          | ~ (v1_subset_1 @ (sk_C @ X4 @ X5) @ (u1_struct_0 @ X5))
% 0.20/0.48          | (v1_tex_2 @ X4 @ X5)
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.20/0.48            (u1_struct_0 @ sk_A))
% 0.20/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('57', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.20/0.48            (u1_struct_0 @ sk_A))
% 0.20/0.48         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['43'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['46', '60'])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) | 
% 0.20/0.48       ~
% 0.20/0.48       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '61'])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) | 
% 0.20/0.48       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['41'])).
% 0.20/0.48  thf('64', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['44', '62', '63'])).
% 0.20/0.48  thf('65', plain, ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['42', '64'])).
% 0.20/0.48  thf('66', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['39', '40', '65', '66'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['43'])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['44', '62'])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48          (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.20/0.48  thf('71', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['67', '70'])).
% 0.20/0.48  thf(fc2_struct_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('72', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.20/0.48          | ~ (l1_struct_0 @ X1)
% 0.20/0.48          | (v2_struct_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.48  thf('73', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.48  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_l1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.48  thf('75', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.48  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.48  thf('77', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['73', '76'])).
% 0.20/0.48  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
