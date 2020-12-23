%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q5KRWU6UNC

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 862 expanded)
%              Number of leaves         :   22 ( 241 expanded)
%              Depth                    :   17
%              Number of atoms          : 1193 (15823 expanded)
%              Number of equality atoms :   33 ( 528 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t13_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_borsuk_1 @ C @ A )
                    & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( C
                    = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                 => ( ( ( v1_borsuk_1 @ B @ A )
                      & ( m1_pre_topc @ B @ A ) )
                  <=> ( ( v1_borsuk_1 @ C @ A )
                      & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_tmap_1])).

thf('0',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t11_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( X10
       != ( u1_struct_0 @ X8 ) )
      | ~ ( v4_pre_topc @ X10 @ X9 )
      | ( v1_borsuk_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_borsuk_1 @ X8 @ X9 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( X11
       != ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( m1_pre_topc @ X11 @ X13 )
      | ( m1_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( m1_pre_topc @ X12 @ X13 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) @ X13 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24','25'])).

thf('27',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('36',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['30'])).

thf('41',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','32','41'])).

thf('43',plain,
    ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
    | ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','42'])).

thf('44',plain,
    ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['30'])).

thf('45',plain,
    ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['30'])).

thf('46',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( X10
       != ( u1_struct_0 @ X8 ) )
      | ~ ( v1_borsuk_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v4_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( v1_borsuk_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('58',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('60',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_pre_topc @ sk_C )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('67',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_pre_topc @ X4 @ X5 )
       != ( g1_pre_topc @ X2 @ X3 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( v1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( v1_pre_topc @ sk_C )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('77',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_borsuk_1 @ X8 @ X9 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
        | ( v1_borsuk_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
        | ( v1_borsuk_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('85',plain,
    ( ( ( v1_borsuk_1 @ sk_B @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','85'])).

thf('87',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['30'])).

thf('88',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['41','45','14','32','88'])).

thf('90',plain,(
    ~ ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['44','89'])).

thf('91',plain,(
    ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) ),
    inference(clc,[status(thm)],['43','90'])).

thf('92',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('93',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','32','41'])).

thf('94',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('96',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( v1_borsuk_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v1_borsuk_1 @ sk_B @ X0 )
        | ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v1_borsuk_1 @ sk_B @ X0 )
        | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','32'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_borsuk_1 @ sk_B @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('106',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
    | ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('107',plain,(
    v1_borsuk_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['41','45','14','32','88','106'])).

thf('108',plain,(
    v1_borsuk_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['105','107'])).

thf('109',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('110',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','32'])).

thf('111',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['109','110'])).

thf('112',plain,(
    v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['102','103','104','108','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['91','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q5KRWU6UNC
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 236 iterations in 0.070s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.21/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(t13_tmap_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.21/0.53               ( ( ( C ) =
% 0.21/0.53                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.21/0.53                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.53                   ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.21/0.53                  ( ( ( C ) =
% 0.21/0.53                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.21/0.53                    ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.53                      ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t13_tmap_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_C @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf(t1_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( m1_subset_1 @
% 0.21/0.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.53          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.53          | ~ (l1_pre_topc @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.53         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(t11_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.53                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.53          | ((X10) != (u1_struct_0 @ X8))
% 0.21/0.53          | ~ (v4_pre_topc @ X10 @ X9)
% 0.21/0.53          | (v1_borsuk_1 @ X8 @ X9)
% 0.21/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.53          | ~ (l1_pre_topc @ X9)
% 0.21/0.53          | ~ (v2_pre_topc @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X9)
% 0.21/0.53          | ~ (l1_pre_topc @ X9)
% 0.21/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.21/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.53          | (v1_borsuk_1 @ X8 @ X9)
% 0.21/0.53          | ~ (v4_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.21/0.53          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.21/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.21/0.53         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.53         | (v1_borsuk_1 @ sk_C @ sk_A)
% 0.21/0.53         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (((~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.53         | (v1_borsuk_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.53      inference('split', [status(esa)], ['13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t12_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.21/0.53               ( ( ( B ) =
% 0.21/0.53                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.21/0.53                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X11)
% 0.21/0.53          | ~ (l1_pre_topc @ X11)
% 0.21/0.53          | ((X11) != (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.21/0.53          | ~ (m1_pre_topc @ X11 @ X13)
% 0.21/0.53          | (m1_pre_topc @ X12 @ X13)
% 0.21/0.53          | ~ (l1_pre_topc @ X12)
% 0.21/0.53          | ~ (v2_pre_topc @ X12)
% 0.21/0.53          | ~ (l1_pre_topc @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X13)
% 0.21/0.53          | ~ (v2_pre_topc @ X12)
% 0.21/0.53          | ~ (l1_pre_topc @ X12)
% 0.21/0.53          | (m1_pre_topc @ X12 @ X13)
% 0.21/0.53          | ~ (m1_pre_topc @ 
% 0.21/0.53               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)) @ X13)
% 0.21/0.53          | ~ (l1_pre_topc @ 
% 0.21/0.53               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.21/0.53          | ~ (v2_pre_topc @ 
% 0.21/0.53               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ sk_C)
% 0.21/0.53          | ~ (v2_pre_topc @ 
% 0.21/0.53               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.53          | ~ (m1_pre_topc @ 
% 0.21/0.53               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.21/0.53          | (m1_pre_topc @ sk_B @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.53  thf('20', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain, ((v2_pre_topc @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.53          | (m1_pre_topc @ sk_B @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['19', '20', '21', '22', '23', '24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '26'])).
% 0.21/0.53  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.21/0.53        | ~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.21/0.53        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.53        | ~ (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (((v1_borsuk_1 @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['33'])).
% 0.21/0.53  thf(t11_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( ( v1_pre_topc @
% 0.21/0.53               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.53             ( m1_pre_topc @
% 0.21/0.53               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X6 @ X7)
% 0.21/0.53          | (m1_pre_topc @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)) @ X7)
% 0.21/0.53          | ~ (l1_pre_topc @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | (m1_pre_topc @ 
% 0.21/0.53            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['30'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain, (((m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['14', '32', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      ((~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.53        | (v1_borsuk_1 @ sk_C @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['12', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      ((~ (v1_borsuk_1 @ sk_C @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_C @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['30'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (~ ((v1_borsuk_1 @ sk_C @ sk_A)) | ~ ((v1_borsuk_1 @ sk_B @ sk_A)) | 
% 0.21/0.53       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.53      inference('split', [status(esa)], ['30'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (((v1_borsuk_1 @ sk_C @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (((v1_borsuk_1 @ sk_C @ sk_A)) <= (((v1_borsuk_1 @ sk_C @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.53          | ((X10) != (u1_struct_0 @ X8))
% 0.21/0.53          | ~ (v1_borsuk_1 @ X8 @ X9)
% 0.21/0.53          | ~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.53          | (v4_pre_topc @ X10 @ X9)
% 0.21/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.53          | ~ (l1_pre_topc @ X9)
% 0.21/0.53          | ~ (v2_pre_topc @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X9)
% 0.21/0.53          | ~ (l1_pre_topc @ X9)
% 0.21/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.21/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.53          | (v4_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.21/0.53          | ~ (v1_borsuk_1 @ X8 @ X9)
% 0.21/0.53          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.21/0.53      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.21/0.53         | ~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.21/0.53         | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.53         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.21/0.53         | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (((v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.21/0.53         <= (((v1_borsuk_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '55'])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['33'])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X6 @ X7)
% 0.21/0.53          | (v1_pre_topc @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.21/0.53          | ~ (l1_pre_topc @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | (v1_pre_topc @ 
% 0.21/0.53            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.53  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('63', plain, (((v1_pre_topc @ sk_C)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(abstractness_v1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ( v1_pre_topc @ A ) =>
% 0.21/0.53         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_pre_topc @ X0)
% 0.21/0.53          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.21/0.53  thf(dt_u1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( m1_subset_1 @
% 0.21/0.53         ( u1_pre_topc @ A ) @ 
% 0.21/0.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X1 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.53          | ~ (l1_pre_topc @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.53  thf(free_g1_pre_topc, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53       ( ![C:$i,D:$i]:
% 0.21/0.53         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.53           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.53         (((g1_pre_topc @ X4 @ X5) != (g1_pre_topc @ X2 @ X3))
% 0.21/0.53          | ((X4) = (X2))
% 0.21/0.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.21/0.53      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ((u1_struct_0 @ X0) = (X1))
% 0.21/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.53              != (g1_pre_topc @ X1 @ X2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_pre_topc @ X0)
% 0.21/0.53          | ((u1_struct_0 @ X0) = (X2))
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '68'])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i]:
% 0.21/0.53         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.21/0.53          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.21/0.53          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['69'])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      ((~ (v1_pre_topc @ sk_C)
% 0.21/0.53        | ~ (l1_pre_topc @ 
% 0.21/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.53        | ((u1_struct_0 @ 
% 0.21/0.53            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.53            = (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['64', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('73', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      ((~ (v1_pre_topc @ sk_C) | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      ((((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['63', '75'])).
% 0.21/0.53  thf('77', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X9)
% 0.21/0.53          | ~ (l1_pre_topc @ X9)
% 0.21/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.21/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.53          | (v1_borsuk_1 @ X8 @ X9)
% 0.21/0.53          | ~ (v4_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.21/0.53          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.21/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.53  thf('78', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53              (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.53           | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.53           | ~ (v4_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.21/0.53           | (v1_borsuk_1 @ sk_B @ X0)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      ((((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['63', '75'])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53              (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.53           | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.53           | ~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.21/0.53           | (v1_borsuk_1 @ sk_B @ X0)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (((~ (v2_pre_topc @ sk_A)
% 0.21/0.53         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | (v1_borsuk_1 @ sk_B @ sk_A)
% 0.21/0.53         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.53         | ~ (m1_pre_topc @ sk_B @ sk_A)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['57', '80'])).
% 0.21/0.53  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('84', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      ((((v1_borsuk_1 @ sk_B @ sk_A)
% 0.21/0.53         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (((v1_borsuk_1 @ sk_B @ sk_A))
% 0.21/0.53         <= (((v1_borsuk_1 @ sk_C @ sk_A)) & 
% 0.21/0.53             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.21/0.53             ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '85'])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      ((~ (v1_borsuk_1 @ sk_B @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['30'])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      (((v1_borsuk_1 @ sk_B @ sk_A)) | ~ ((v1_borsuk_1 @ sk_C @ sk_A)) | 
% 0.21/0.53       ~ ((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.53  thf('89', plain, (~ ((v1_borsuk_1 @ sk_C @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)],
% 0.21/0.53                ['41', '45', '14', '32', '88'])).
% 0.21/0.53  thf('90', plain, (~ (v1_borsuk_1 @ sk_C @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['44', '89'])).
% 0.21/0.53  thf('91', plain, (~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)),
% 0.21/0.53      inference('clc', [status(thm)], ['43', '90'])).
% 0.21/0.53  thf('92', plain,
% 0.21/0.53      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('93', plain, (((m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['14', '32', '41'])).
% 0.21/0.53  thf('94', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.21/0.53  thf('95', plain,
% 0.21/0.53      ((((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['63', '75'])).
% 0.21/0.53  thf('96', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X9)
% 0.21/0.53          | ~ (l1_pre_topc @ X9)
% 0.21/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.21/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.53          | (v4_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.21/0.53          | ~ (v1_borsuk_1 @ X8 @ X9)
% 0.21/0.53          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.21/0.53      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.53  thf('97', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53              (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.53           | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.53           | ~ (v1_borsuk_1 @ sk_B @ X0)
% 0.21/0.53           | (v4_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.53  thf('98', plain,
% 0.21/0.53      ((((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['63', '75'])).
% 0.21/0.53  thf('99', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53              (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.53           | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.53           | ~ (v1_borsuk_1 @ sk_B @ X0)
% 0.21/0.53           | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)))
% 0.21/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['97', '98'])).
% 0.21/0.53  thf('100', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['14', '32'])).
% 0.21/0.53  thf('101', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.53          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.53          | ~ (v1_borsuk_1 @ sk_B @ X0)
% 0.21/0.53          | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['99', '100'])).
% 0.21/0.53  thf('102', plain,
% 0.21/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.53        | ~ (v1_borsuk_1 @ sk_B @ sk_A)
% 0.21/0.53        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['94', '101'])).
% 0.21/0.53  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('105', plain,
% 0.21/0.53      (((v1_borsuk_1 @ sk_B @ sk_A)) <= (((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['46'])).
% 0.21/0.53  thf('106', plain,
% 0.21/0.53      (((v1_borsuk_1 @ sk_B @ sk_A)) | ((v1_borsuk_1 @ sk_C @ sk_A))),
% 0.21/0.53      inference('split', [status(esa)], ['46'])).
% 0.21/0.53  thf('107', plain, (((v1_borsuk_1 @ sk_B @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)],
% 0.21/0.53                ['41', '45', '14', '32', '88', '106'])).
% 0.21/0.53  thf('108', plain, ((v1_borsuk_1 @ sk_B @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['105', '107'])).
% 0.21/0.53  thf('109', plain,
% 0.21/0.53      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['33'])).
% 0.21/0.53  thf('110', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['14', '32'])).
% 0.21/0.53  thf('111', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 0.21/0.53  thf('112', plain, ((v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['102', '103', '104', '108', '111'])).
% 0.21/0.53  thf('113', plain, ($false), inference('demod', [status(thm)], ['91', '112'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
