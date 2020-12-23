%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2LxGCl1EsM

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:58 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 313 expanded)
%              Number of leaves         :   23 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          : 1067 (4982 expanded)
%              Number of equality atoms :   49 ( 192 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(t116_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( v1_tsep_1 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k8_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( ( v1_tsep_1 @ B @ A )
                & ( m1_pre_topc @ B @ A ) )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k8_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_tmap_1])).

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k8_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( C
                        = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( X2
       != ( k8_tmap_1 @ X1 @ X0 ) )
      | ( X3
       != ( u1_struct_0 @ X0 ) )
      | ( X2
        = ( k6_tmap_1 @ X1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( ( k8_tmap_1 @ X1 @ X0 )
        = ( k6_tmap_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('16',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('24',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','21','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('37',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('44',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf(t106_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
       != ( k6_tmap_1 @ X10 @ X9 ) )
      | ( v3_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('53',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tsep_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( ( sk_C @ X4 @ X5 )
        = ( u1_struct_0 @ X4 ) )
      | ( v1_tsep_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( v3_pre_topc @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ( v1_tsep_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('65',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('73',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('74',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('75',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( v1_tsep_1 @ X4 @ X5 )
      | ( X6
       != ( u1_struct_0 @ X4 ) )
      | ( v3_pre_topc @ X6 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('76',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X4 ) @ X5 )
      | ~ ( v1_tsep_1 @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','80'])).

thf('82',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
        = ( k6_tmap_1 @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','4','71','72','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2LxGCl1EsM
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:05:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 54 iterations in 0.093s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.37/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.37/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.37/0.56  thf(t116_tmap_1, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.56           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.37/0.56             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.56               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.56              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.37/0.56                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.56                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.37/0.56        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.37/0.56       ~
% 0.37/0.56       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.37/0.56       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('4', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('5', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t1_tsep_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.56           ( m1_subset_1 @
% 0.37/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.37/0.56          | (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.56          | ~ (l1_pre_topc @ X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf(d11_tmap_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.37/0.56                 ( l1_pre_topc @ C ) ) =>
% 0.37/0.56               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.37/0.56                 ( ![D:$i]:
% 0.37/0.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.37/0.56                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X0 @ X1)
% 0.37/0.56          | ((X2) != (k8_tmap_1 @ X1 @ X0))
% 0.37/0.56          | ((X3) != (u1_struct_0 @ X0))
% 0.37/0.56          | ((X2) = (k6_tmap_1 @ X1 @ X3))
% 0.37/0.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.37/0.56          | ~ (l1_pre_topc @ X2)
% 0.37/0.56          | ~ (v2_pre_topc @ X2)
% 0.37/0.56          | ~ (v1_pre_topc @ X2)
% 0.37/0.56          | ~ (l1_pre_topc @ X1)
% 0.37/0.56          | ~ (v2_pre_topc @ X1)
% 0.37/0.56          | (v2_struct_0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((v2_struct_0 @ X1)
% 0.37/0.56          | ~ (v2_pre_topc @ X1)
% 0.37/0.56          | ~ (l1_pre_topc @ X1)
% 0.37/0.56          | ~ (v1_pre_topc @ (k8_tmap_1 @ X1 @ X0))
% 0.37/0.56          | ~ (v2_pre_topc @ (k8_tmap_1 @ X1 @ X0))
% 0.37/0.56          | ~ (l1_pre_topc @ (k8_tmap_1 @ X1 @ X0))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.37/0.56          | ((k8_tmap_1 @ X1 @ X0) = (k6_tmap_1 @ X1 @ (u1_struct_0 @ X0)))
% 0.37/0.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.37/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.37/0.56        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.37/0.56            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.37/0.56        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '11'])).
% 0.37/0.56  thf('13', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(dt_k8_tmap_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.56       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.37/0.56         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.37/0.56         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X7)
% 0.37/0.56          | ~ (v2_pre_topc @ X7)
% 0.37/0.56          | (v2_struct_0 @ X7)
% 0.37/0.56          | ~ (m1_pre_topc @ X8 @ X7)
% 0.37/0.56          | (l1_pre_topc @ (k8_tmap_1 @ X7 @ X8)))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.37/0.56  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('21', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['19', '20'])).
% 0.37/0.56  thf('22', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X7)
% 0.37/0.56          | ~ (v2_pre_topc @ X7)
% 0.37/0.56          | (v2_struct_0 @ X7)
% 0.37/0.56          | ~ (m1_pre_topc @ X8 @ X7)
% 0.37/0.56          | (v2_pre_topc @ (k8_tmap_1 @ X7 @ X8)))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.37/0.56  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('29', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.37/0.56        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['12', '13', '21', '29', '30', '31'])).
% 0.37/0.56  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      ((~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.37/0.56            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.37/0.56      inference('clc', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X7)
% 0.37/0.56          | ~ (v2_pre_topc @ X7)
% 0.37/0.56          | (v2_struct_0 @ X7)
% 0.37/0.56          | ~ (m1_pre_topc @ X8 @ X7)
% 0.37/0.56          | (v1_pre_topc @ (k8_tmap_1 @ X7 @ X8)))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.37/0.56  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('42', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['40', '41'])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['34', '42'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['44'])).
% 0.37/0.56  thf(t106_tmap_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.37/0.56             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.56               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.37/0.56          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 0.37/0.56              != (k6_tmap_1 @ X10 @ X9))
% 0.37/0.56          | (v3_pre_topc @ X9 @ X10)
% 0.37/0.56          | ~ (l1_pre_topc @ X10)
% 0.37/0.56          | ~ (v2_pre_topc @ X10)
% 0.37/0.56          | (v2_struct_0 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t106_tmap_1])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 0.37/0.56           | (v2_struct_0 @ sk_A)
% 0.37/0.56           | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56           | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56           | (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 0.37/0.56           | (v2_struct_0 @ sk_A)
% 0.37/0.56           | (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.56              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.56         | (v2_struct_0 @ sk_A)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['43', '50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.56         | (v2_struct_0 @ sk_A)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A) | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['53'])).
% 0.37/0.56  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.37/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('clc', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d1_tsep_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.56           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.37/0.56             ( ![C:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X4 @ X5)
% 0.37/0.56          | ((sk_C @ X4 @ X5) = (u1_struct_0 @ X4))
% 0.37/0.56          | (v1_tsep_1 @ X4 @ X5)
% 0.37/0.56          | ~ (l1_pre_topc @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.56        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.56  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.56        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.37/0.56         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X4 @ X5)
% 0.37/0.56          | ~ (v3_pre_topc @ (sk_C @ X4 @ X5) @ X5)
% 0.37/0.56          | (v1_tsep_1 @ X4 @ X5)
% 0.37/0.56          | ~ (l1_pre_topc @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.56         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.37/0.56  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('67', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.56         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.37/0.56         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('clc', [status(thm)], ['68', '69'])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.37/0.56       ~
% 0.37/0.56       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['56', '70'])).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.37/0.56       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('split', [status(esa)], ['44'])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['44'])).
% 0.37/0.56  thf('74', plain,
% 0.37/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X4 @ X5)
% 0.37/0.56          | ~ (v1_tsep_1 @ X4 @ X5)
% 0.37/0.56          | ((X6) != (u1_struct_0 @ X4))
% 0.37/0.56          | (v3_pre_topc @ X6 @ X5)
% 0.37/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.37/0.56          | ~ (l1_pre_topc @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.37/0.56  thf('76', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X5)
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X4) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.37/0.56          | (v3_pre_topc @ (u1_struct_0 @ X4) @ X5)
% 0.37/0.56          | ~ (v1_tsep_1 @ X4 @ X5)
% 0.37/0.56          | ~ (m1_pre_topc @ X4 @ X5))),
% 0.37/0.56      inference('simplify', [status(thm)], ['75'])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.37/0.56        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.56        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['74', '76'])).
% 0.37/0.56  thf('78', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('80', plain,
% 0.37/0.56      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.56        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.37/0.56  thf('81', plain,
% 0.37/0.56      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.37/0.56         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['73', '80'])).
% 0.37/0.56  thf('82', plain,
% 0.37/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('83', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.37/0.56          | ~ (v3_pre_topc @ X9 @ X10)
% 0.37/0.56          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 0.37/0.56              = (k6_tmap_1 @ X10 @ X9))
% 0.37/0.56          | ~ (l1_pre_topc @ X10)
% 0.37/0.56          | ~ (v2_pre_topc @ X10)
% 0.37/0.56          | (v2_struct_0 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t106_tmap_1])).
% 0.37/0.56  thf('84', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.37/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['82', '83'])).
% 0.37/0.56  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('87', plain,
% 0.37/0.56      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['34', '42'])).
% 0.37/0.56  thf('88', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56            = (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.37/0.56  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('90', plain,
% 0.37/0.56      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.56        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56            = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('clc', [status(thm)], ['88', '89'])).
% 0.37/0.56  thf('91', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['81', '90'])).
% 0.37/0.56  thf('92', plain,
% 0.37/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('93', plain,
% 0.37/0.56      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.37/0.56             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['91', '92'])).
% 0.37/0.56  thf('94', plain,
% 0.37/0.56      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.37/0.56       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['93'])).
% 0.37/0.56  thf('95', plain, ($false),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['1', '4', '71', '72', '94'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
