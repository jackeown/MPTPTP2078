%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DyxeEfBrhR

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:09 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  199 (7748 expanded)
%              Number of leaves         :   28 (2325 expanded)
%              Depth                    :   28
%              Number of atoms          : 1575 (111210 expanded)
%              Number of equality atoms :   49 (3642 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t14_tmap_1,conjecture,(
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
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_tsep_1 @ C @ A )
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
                 => ( ( ( v1_tsep_1 @ B @ A )
                      & ( m1_pre_topc @ B @ A ) )
                  <=> ( ( v1_tsep_1 @ C @ A )
                      & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tmap_1])).

thf('0',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) ) ) )
      | ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('23',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('35',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43','44','47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['32','50'])).

thf('52',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['32','50'])).

thf('54',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('56',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('60',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('62',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','63'])).

thf('65',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('67',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X1 )
      | ( v1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('73',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('74',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('77',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('82',plain,
    ( ( ( v1_tsep_1 @ sk_C @ sk_A )
      | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71','74','80','81'])).

thf('83',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','56'])).

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

thf('88',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( X14
       != ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X16 )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('89',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) @ X16 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_C
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('95',plain,
    ( sk_C
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('98',plain,
    ( sk_C
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('99',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('101',plain,
    ( sk_C
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['90','95','96','97','98','99','100','101','102','103'])).

thf('105',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['86','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['108'])).

thf('110',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['107','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['84','110'])).

thf('112',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','111'])).

thf('113',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['108'])).

thf('114',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('115',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['108'])).

thf('116',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['108'])).

thf('118',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
   <= ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['118'])).

thf('120',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','63'])).

thf('121',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('123',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_tsep_1 @ X0 @ X1 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['121','123'])).

thf('125',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( v1_tsep_1 @ sk_C @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','124'])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('129',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('130',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('131',plain,
    ( ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
      | ~ ( v1_tsep_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130'])).

thf('132',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','131'])).

thf('133',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','63'])).

thf('134',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('135',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ( v1_tsep_1 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ X0 )
      | ( v1_tsep_1 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('143',plain,
    ( ( ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( ( v1_tsep_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','143'])).

thf('145',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['108'])).

thf('146',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['116','117','84','110','146'])).

thf('148',plain,(
    ~ ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['113','147'])).

thf('149',plain,(
    ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ) ),
    inference(clc,[status(thm)],['112','148'])).

thf('150',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','63'])).

thf('151',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['84','110'])).

thf('152',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('154',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_tsep_1 @ sk_B @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_tsep_1 @ sk_B @ X0 )
      | ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['152','157'])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['118'])).

thf('162',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['118'])).

thf('163',plain,(
    v1_tsep_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['116','117','84','110','146','162'])).

thf('164',plain,(
    v1_tsep_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['161','163'])).

thf('165',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('166',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['84','110'])).

thf('167',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['165','166'])).

thf('168',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['158','159','160','164','167'])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['149','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DyxeEfBrhR
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.64/0.88  % Solved by: fo/fo7.sh
% 0.64/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.88  % done 1005 iterations in 0.427s
% 0.64/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.64/0.88  % SZS output start Refutation
% 0.64/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.64/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.88  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.64/0.88  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.64/0.88  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.64/0.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.64/0.88  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.64/0.88  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.64/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.88  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.64/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.64/0.88  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.64/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.64/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.64/0.88  thf(t14_tmap_1, conjecture,
% 0.64/0.88    (![A:$i]:
% 0.64/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.88       ( ![B:$i]:
% 0.64/0.88         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.64/0.88           ( ![C:$i]:
% 0.64/0.88             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.64/0.88               ( ( ( C ) =
% 0.64/0.88                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.64/0.88                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.64/0.88                   ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.64/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.88    (~( ![A:$i]:
% 0.64/0.88        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.88          ( ![B:$i]:
% 0.64/0.88            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.64/0.88              ( ![C:$i]:
% 0.64/0.88                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.64/0.88                  ( ( ( C ) =
% 0.64/0.88                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.64/0.88                    ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.64/0.88                      ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.64/0.88    inference('cnf.neg', [status(esa)], [t14_tmap_1])).
% 0.64/0.88  thf('0', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('1', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['0'])).
% 0.64/0.88  thf(t1_tsep_1, axiom,
% 0.64/0.88    (![A:$i]:
% 0.64/0.88     ( ( l1_pre_topc @ A ) =>
% 0.64/0.88       ( ![B:$i]:
% 0.64/0.88         ( ( m1_pre_topc @ B @ A ) =>
% 0.64/0.88           ( m1_subset_1 @
% 0.64/0.88             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.64/0.88  thf('2', plain,
% 0.64/0.88      (![X20 : $i, X21 : $i]:
% 0.64/0.88         (~ (m1_pre_topc @ X20 @ X21)
% 0.64/0.88          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.64/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.64/0.88          | ~ (l1_pre_topc @ X21))),
% 0.64/0.88      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.64/0.88  thf('3', plain,
% 0.64/0.88      (((~ (l1_pre_topc @ sk_A)
% 0.64/0.88         | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.64/0.88            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.64/0.88         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.64/0.88  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf(fc10_tops_1, axiom,
% 0.64/0.88    (![A:$i]:
% 0.64/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.88       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.64/0.88  thf('5', plain,
% 0.64/0.88      (![X11 : $i]:
% 0.64/0.88         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.64/0.88          | ~ (l1_pre_topc @ X11)
% 0.64/0.88          | ~ (v2_pre_topc @ X11))),
% 0.64/0.88      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.64/0.88  thf(d3_struct_0, axiom,
% 0.64/0.88    (![A:$i]:
% 0.64/0.88     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.64/0.88  thf('6', plain,
% 0.64/0.88      (![X6 : $i]:
% 0.64/0.88         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.64/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.64/0.88  thf('7', plain,
% 0.64/0.88      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf(d10_xboole_0, axiom,
% 0.64/0.88    (![A:$i,B:$i]:
% 0.64/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.64/0.88  thf('8', plain,
% 0.64/0.88      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.64/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.64/0.88  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.64/0.88      inference('simplify', [status(thm)], ['8'])).
% 0.64/0.88  thf(t3_subset, axiom,
% 0.64/0.88    (![A:$i,B:$i]:
% 0.64/0.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.64/0.88  thf('10', plain,
% 0.64/0.88      (![X3 : $i, X5 : $i]:
% 0.64/0.88         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.64/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.88  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.64/0.88      inference('sup-', [status(thm)], ['9', '10'])).
% 0.64/0.88  thf(t60_pre_topc, axiom,
% 0.64/0.88    (![A:$i]:
% 0.64/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.88       ( ![B:$i]:
% 0.64/0.88         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.64/0.88             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.64/0.88           ( ( v3_pre_topc @
% 0.64/0.88               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.64/0.88             ( m1_subset_1 @
% 0.64/0.88               B @ 
% 0.64/0.88               ( k1_zfmisc_1 @
% 0.64/0.88                 ( u1_struct_0 @
% 0.64/0.88                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.64/0.88  thf('12', plain,
% 0.64/0.88      (![X8 : $i, X9 : $i]:
% 0.64/0.88         (~ (v3_pre_topc @ X8 @ 
% 0.64/0.88             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.64/0.88          | ~ (m1_subset_1 @ X8 @ 
% 0.64/0.88               (k1_zfmisc_1 @ 
% 0.64/0.88                (u1_struct_0 @ 
% 0.64/0.88                 (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))))
% 0.64/0.88          | (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.64/0.88          | ~ (l1_pre_topc @ X9)
% 0.64/0.88          | ~ (v2_pre_topc @ X9))),
% 0.64/0.88      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.64/0.88  thf('13', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (v2_pre_topc @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | (m1_subset_1 @ 
% 0.64/0.88             (u1_struct_0 @ 
% 0.64/0.88              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.64/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.64/0.88          | ~ (v3_pre_topc @ 
% 0.64/0.88               (u1_struct_0 @ 
% 0.64/0.88                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.64/0.88      inference('sup-', [status(thm)], ['11', '12'])).
% 0.64/0.88  thf('14', plain,
% 0.64/0.88      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ 
% 0.64/0.88           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.64/0.88        | (m1_subset_1 @ 
% 0.64/0.88           (u1_struct_0 @ 
% 0.64/0.88            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.64/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.64/0.88        | ~ (l1_pre_topc @ sk_B)
% 0.64/0.88        | ~ (v2_pre_topc @ sk_B))),
% 0.64/0.88      inference('sup-', [status(thm)], ['7', '13'])).
% 0.64/0.88  thf('15', plain,
% 0.64/0.88      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('16', plain,
% 0.64/0.88      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('18', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('19', plain,
% 0.64/0.88      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.64/0.88        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.64/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.64/0.88      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.88  thf('20', plain,
% 0.64/0.88      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 0.64/0.88        | ~ (l1_struct_0 @ sk_C)
% 0.64/0.88        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.64/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.64/0.88      inference('sup-', [status(thm)], ['6', '19'])).
% 0.64/0.88  thf('21', plain, ((l1_pre_topc @ sk_C)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf(dt_l1_pre_topc, axiom,
% 0.64/0.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.64/0.88  thf('22', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.64/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.64/0.88  thf('23', plain, ((l1_struct_0 @ sk_C)),
% 0.64/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.64/0.88  thf('24', plain,
% 0.64/0.88      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 0.64/0.88        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.64/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.64/0.88      inference('demod', [status(thm)], ['20', '23'])).
% 0.64/0.88  thf('25', plain,
% 0.64/0.88      ((~ (v2_pre_topc @ sk_C)
% 0.64/0.88        | ~ (l1_pre_topc @ sk_C)
% 0.64/0.88        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.64/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.64/0.88      inference('sup-', [status(thm)], ['5', '24'])).
% 0.64/0.88  thf('26', plain, ((v2_pre_topc @ sk_C)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('27', plain, ((l1_pre_topc @ sk_C)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('28', plain,
% 0.64/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.64/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.64/0.88      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.64/0.88  thf('29', plain,
% 0.64/0.88      (![X3 : $i, X4 : $i]:
% 0.64/0.88         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.64/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.88  thf('30', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.64/0.88      inference('sup-', [status(thm)], ['28', '29'])).
% 0.64/0.88  thf('31', plain,
% 0.64/0.88      (![X0 : $i, X2 : $i]:
% 0.64/0.88         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.64/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.64/0.88  thf('32', plain,
% 0.64/0.88      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.64/0.88        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.64/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.64/0.88  thf('33', plain,
% 0.64/0.88      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('34', plain,
% 0.64/0.88      (![X11 : $i]:
% 0.64/0.88         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.64/0.88          | ~ (l1_pre_topc @ X11)
% 0.64/0.88          | ~ (v2_pre_topc @ X11))),
% 0.64/0.88      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.64/0.88  thf('35', plain,
% 0.64/0.88      (![X6 : $i]:
% 0.64/0.88         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.64/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.64/0.88  thf('36', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.64/0.88      inference('sup-', [status(thm)], ['9', '10'])).
% 0.64/0.88  thf('37', plain,
% 0.64/0.88      (![X9 : $i, X10 : $i]:
% 0.64/0.88         (~ (v3_pre_topc @ X10 @ X9)
% 0.64/0.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.64/0.88          | (m1_subset_1 @ X10 @ 
% 0.64/0.88             (k1_zfmisc_1 @ 
% 0.64/0.88              (u1_struct_0 @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))))
% 0.64/0.88          | ~ (l1_pre_topc @ X9)
% 0.64/0.88          | ~ (v2_pre_topc @ X9))),
% 0.64/0.88      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.64/0.88  thf('38', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (v2_pre_topc @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.64/0.88             (k1_zfmisc_1 @ 
% 0.64/0.88              (u1_struct_0 @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.64/0.88          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.64/0.88      inference('sup-', [status(thm)], ['36', '37'])).
% 0.64/0.88  thf('39', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.64/0.88          | ~ (l1_struct_0 @ X0)
% 0.64/0.88          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.64/0.88             (k1_zfmisc_1 @ 
% 0.64/0.88              (u1_struct_0 @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | ~ (v2_pre_topc @ X0))),
% 0.64/0.88      inference('sup-', [status(thm)], ['35', '38'])).
% 0.64/0.88  thf('40', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (v2_pre_topc @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | ~ (v2_pre_topc @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.64/0.88             (k1_zfmisc_1 @ 
% 0.64/0.88              (u1_struct_0 @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.64/0.88          | ~ (l1_struct_0 @ X0))),
% 0.64/0.88      inference('sup-', [status(thm)], ['34', '39'])).
% 0.64/0.88  thf('41', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (l1_struct_0 @ X0)
% 0.64/0.88          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.64/0.88             (k1_zfmisc_1 @ 
% 0.64/0.88              (u1_struct_0 @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | ~ (v2_pre_topc @ X0))),
% 0.64/0.88      inference('simplify', [status(thm)], ['40'])).
% 0.64/0.88  thf('42', plain,
% 0.64/0.88      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.64/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.64/0.88        | ~ (v2_pre_topc @ sk_B)
% 0.64/0.88        | ~ (l1_pre_topc @ sk_B)
% 0.64/0.88        | ~ (l1_struct_0 @ sk_B))),
% 0.64/0.88      inference('sup+', [status(thm)], ['33', '41'])).
% 0.64/0.88  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('46', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.64/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.64/0.88  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.64/0.88      inference('sup-', [status(thm)], ['45', '46'])).
% 0.64/0.88  thf('48', plain,
% 0.64/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.64/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.64/0.88      inference('demod', [status(thm)], ['42', '43', '44', '47'])).
% 0.64/0.88  thf('49', plain,
% 0.64/0.88      (![X3 : $i, X4 : $i]:
% 0.64/0.88         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.64/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.88  thf('50', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.64/0.88      inference('sup-', [status(thm)], ['48', '49'])).
% 0.64/0.88  thf('51', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['32', '50'])).
% 0.64/0.88  thf('52', plain,
% 0.64/0.88      (![X6 : $i]:
% 0.64/0.88         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.64/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.64/0.88  thf('53', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['32', '50'])).
% 0.64/0.88  thf('54', plain,
% 0.64/0.88      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_B))),
% 0.64/0.88      inference('sup+', [status(thm)], ['52', '53'])).
% 0.64/0.88  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.64/0.88      inference('sup-', [status(thm)], ['45', '46'])).
% 0.64/0.88  thf('56', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['54', '55'])).
% 0.64/0.88  thf('57', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.64/0.88      inference('demod', [status(thm)], ['51', '56'])).
% 0.64/0.88  thf('58', plain,
% 0.64/0.88      (![X6 : $i]:
% 0.64/0.88         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.64/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.64/0.88  thf('59', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['54', '55'])).
% 0.64/0.88  thf('60', plain,
% 0.64/0.88      ((((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.64/0.88      inference('sup+', [status(thm)], ['58', '59'])).
% 0.64/0.88  thf('61', plain, ((l1_struct_0 @ sk_C)),
% 0.64/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.64/0.88  thf('62', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['60', '61'])).
% 0.64/0.88  thf('63', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['57', '62'])).
% 0.64/0.88  thf('64', plain,
% 0.64/0.88      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.64/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.64/0.88         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['3', '4', '63'])).
% 0.64/0.88  thf('65', plain,
% 0.64/0.88      (![X6 : $i]:
% 0.64/0.88         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.64/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.64/0.88  thf(t16_tsep_1, axiom,
% 0.64/0.88    (![A:$i]:
% 0.64/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.88       ( ![B:$i]:
% 0.64/0.88         ( ( m1_pre_topc @ B @ A ) =>
% 0.64/0.88           ( ![C:$i]:
% 0.64/0.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.88               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.64/0.88                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.64/0.88                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.64/0.88  thf('66', plain,
% 0.64/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.64/0.88         (~ (m1_pre_topc @ X17 @ X18)
% 0.64/0.88          | ((X19) != (u1_struct_0 @ X17))
% 0.64/0.88          | ~ (v3_pre_topc @ X19 @ X18)
% 0.64/0.88          | (v1_tsep_1 @ X17 @ X18)
% 0.64/0.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.64/0.88          | ~ (l1_pre_topc @ X18)
% 0.64/0.88          | ~ (v2_pre_topc @ X18))),
% 0.64/0.88      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.64/0.88  thf('67', plain,
% 0.64/0.88      (![X17 : $i, X18 : $i]:
% 0.64/0.88         (~ (v2_pre_topc @ X18)
% 0.64/0.88          | ~ (l1_pre_topc @ X18)
% 0.64/0.88          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.64/0.88               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.64/0.88          | (v1_tsep_1 @ X17 @ X18)
% 0.64/0.88          | ~ (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.64/0.88          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.64/0.88      inference('simplify', [status(thm)], ['66'])).
% 0.64/0.88  thf('68', plain,
% 0.64/0.88      (![X0 : $i, X1 : $i]:
% 0.64/0.88         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.64/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.64/0.88          | ~ (l1_struct_0 @ X0)
% 0.64/0.88          | ~ (m1_pre_topc @ X0 @ X1)
% 0.64/0.88          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X1)
% 0.64/0.88          | (v1_tsep_1 @ X0 @ X1)
% 0.64/0.88          | ~ (l1_pre_topc @ X1)
% 0.64/0.88          | ~ (v2_pre_topc @ X1))),
% 0.64/0.88      inference('sup-', [status(thm)], ['65', '67'])).
% 0.64/0.88  thf('69', plain,
% 0.64/0.88      (((~ (v2_pre_topc @ sk_A)
% 0.64/0.88         | ~ (l1_pre_topc @ sk_A)
% 0.64/0.88         | (v1_tsep_1 @ sk_C @ sk_A)
% 0.64/0.88         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.64/0.88         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.64/0.88         | ~ (l1_struct_0 @ sk_C))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('sup-', [status(thm)], ['64', '68'])).
% 0.64/0.88  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('72', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['54', '55'])).
% 0.64/0.88  thf('73', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['60', '61'])).
% 0.64/0.88  thf('74', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['72', '73'])).
% 0.64/0.88  thf('75', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['0'])).
% 0.64/0.88  thf(t11_tmap_1, axiom,
% 0.64/0.88    (![A:$i]:
% 0.64/0.88     ( ( l1_pre_topc @ A ) =>
% 0.64/0.88       ( ![B:$i]:
% 0.64/0.88         ( ( m1_pre_topc @ B @ A ) =>
% 0.64/0.88           ( ( v1_pre_topc @
% 0.64/0.88               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.64/0.88             ( m1_pre_topc @
% 0.64/0.88               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.64/0.88  thf('76', plain,
% 0.64/0.88      (![X12 : $i, X13 : $i]:
% 0.64/0.88         (~ (m1_pre_topc @ X12 @ X13)
% 0.64/0.88          | (m1_pre_topc @ 
% 0.64/0.88             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)) @ X13)
% 0.64/0.88          | ~ (l1_pre_topc @ X13))),
% 0.64/0.88      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.64/0.88  thf('77', plain,
% 0.64/0.88      (((~ (l1_pre_topc @ sk_A)
% 0.64/0.88         | (m1_pre_topc @ 
% 0.64/0.88            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)))
% 0.64/0.88         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('sup-', [status(thm)], ['75', '76'])).
% 0.64/0.88  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('79', plain,
% 0.64/0.88      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('80', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.64/0.88  thf('81', plain, ((l1_struct_0 @ sk_C)),
% 0.64/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.64/0.88  thf('82', plain,
% 0.64/0.88      ((((v1_tsep_1 @ sk_C @ sk_A)
% 0.64/0.88         | ~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)))
% 0.64/0.88         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['69', '70', '71', '74', '80', '81'])).
% 0.64/0.88  thf('83', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('84', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.64/0.88      inference('split', [status(esa)], ['83'])).
% 0.64/0.88  thf('85', plain, (((m1_pre_topc @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('86', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['85'])).
% 0.64/0.88  thf('87', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.64/0.88      inference('demod', [status(thm)], ['51', '56'])).
% 0.64/0.88  thf(t12_tmap_1, axiom,
% 0.64/0.88    (![A:$i]:
% 0.64/0.88     ( ( l1_pre_topc @ A ) =>
% 0.64/0.88       ( ![B:$i]:
% 0.64/0.88         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.64/0.88           ( ![C:$i]:
% 0.64/0.88             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.64/0.88               ( ( ( B ) =
% 0.64/0.88                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.64/0.88                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.64/0.88  thf('88', plain,
% 0.64/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.88         (~ (v2_pre_topc @ X14)
% 0.64/0.88          | ~ (l1_pre_topc @ X14)
% 0.64/0.88          | ((X14) != (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.64/0.88          | ~ (m1_pre_topc @ X14 @ X16)
% 0.64/0.88          | (m1_pre_topc @ X15 @ X16)
% 0.64/0.88          | ~ (l1_pre_topc @ X15)
% 0.64/0.88          | ~ (v2_pre_topc @ X15)
% 0.64/0.88          | ~ (l1_pre_topc @ X16))),
% 0.64/0.88      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.64/0.88  thf('89', plain,
% 0.64/0.88      (![X15 : $i, X16 : $i]:
% 0.64/0.88         (~ (l1_pre_topc @ X16)
% 0.64/0.88          | ~ (v2_pre_topc @ X15)
% 0.64/0.88          | ~ (l1_pre_topc @ X15)
% 0.64/0.88          | (m1_pre_topc @ X15 @ X16)
% 0.64/0.88          | ~ (m1_pre_topc @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)) @ X16)
% 0.64/0.88          | ~ (l1_pre_topc @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.64/0.88          | ~ (v2_pre_topc @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15))))),
% 0.64/0.88      inference('simplify', [status(thm)], ['88'])).
% 0.64/0.88  thf('90', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (l1_pre_topc @ 
% 0.64/0.88             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.64/0.88          | ~ (v2_pre_topc @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.64/0.88          | ~ (m1_pre_topc @ 
% 0.64/0.88               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.64/0.88          | (m1_pre_topc @ sk_B @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ sk_B)
% 0.64/0.88          | ~ (v2_pre_topc @ sk_B)
% 0.64/0.88          | ~ (l1_pre_topc @ X0))),
% 0.64/0.88      inference('sup-', [status(thm)], ['87', '89'])).
% 0.64/0.88  thf('91', plain,
% 0.64/0.88      (![X6 : $i]:
% 0.64/0.88         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.64/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.64/0.88  thf('92', plain,
% 0.64/0.88      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('93', plain,
% 0.64/0.88      ((((sk_C) = (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.64/0.88        | ~ (l1_struct_0 @ sk_B))),
% 0.64/0.88      inference('sup+', [status(thm)], ['91', '92'])).
% 0.64/0.88  thf('94', plain, ((l1_struct_0 @ sk_B)),
% 0.64/0.88      inference('sup-', [status(thm)], ['45', '46'])).
% 0.64/0.88  thf('95', plain,
% 0.64/0.88      (((sk_C) = (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.64/0.88      inference('demod', [status(thm)], ['93', '94'])).
% 0.64/0.88  thf('96', plain, ((l1_pre_topc @ sk_C)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('97', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.64/0.88      inference('demod', [status(thm)], ['51', '56'])).
% 0.64/0.88  thf('98', plain,
% 0.64/0.88      (((sk_C) = (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.64/0.88      inference('demod', [status(thm)], ['93', '94'])).
% 0.64/0.88  thf('99', plain, ((v2_pre_topc @ sk_C)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('100', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.64/0.88      inference('demod', [status(thm)], ['51', '56'])).
% 0.64/0.88  thf('101', plain,
% 0.64/0.88      (((sk_C) = (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.64/0.88      inference('demod', [status(thm)], ['93', '94'])).
% 0.64/0.88  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('103', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('104', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (m1_pre_topc @ sk_C @ X0)
% 0.64/0.88          | (m1_pre_topc @ sk_B @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ X0))),
% 0.64/0.88      inference('demod', [status(thm)],
% 0.64/0.88                ['90', '95', '96', '97', '98', '99', '100', '101', '102', '103'])).
% 0.64/0.88  thf('105', plain,
% 0.64/0.88      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A)))
% 0.64/0.88         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.64/0.88      inference('sup-', [status(thm)], ['86', '104'])).
% 0.64/0.88  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('107', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['105', '106'])).
% 0.64/0.88  thf('108', plain,
% 0.64/0.88      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.64/0.88        | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.64/0.88        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.64/0.88        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('109', plain,
% 0.64/0.88      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['108'])).
% 0.64/0.88  thf('110', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.64/0.88      inference('sup-', [status(thm)], ['107', '109'])).
% 0.64/0.88  thf('111', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.64/0.88      inference('sat_resolution*', [status(thm)], ['84', '110'])).
% 0.64/0.88  thf('112', plain,
% 0.64/0.88      (((v1_tsep_1 @ sk_C @ sk_A)
% 0.64/0.88        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A))),
% 0.64/0.88      inference('simpl_trail', [status(thm)], ['82', '111'])).
% 0.64/0.88  thf('113', plain,
% 0.64/0.88      ((~ (v1_tsep_1 @ sk_C @ sk_A)) <= (~ ((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['108'])).
% 0.64/0.88  thf('114', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.64/0.88  thf('115', plain,
% 0.64/0.88      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['108'])).
% 0.64/0.88  thf('116', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.64/0.88      inference('sup-', [status(thm)], ['114', '115'])).
% 0.64/0.88  thf('117', plain,
% 0.64/0.88      (~ ((v1_tsep_1 @ sk_C @ sk_A)) | ~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.64/0.88       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.64/0.88      inference('split', [status(esa)], ['108'])).
% 0.64/0.88  thf('118', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('119', plain,
% 0.64/0.88      (((v1_tsep_1 @ sk_C @ sk_A)) <= (((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['118'])).
% 0.64/0.88  thf('120', plain,
% 0.64/0.88      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.64/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.64/0.88         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['3', '4', '63'])).
% 0.64/0.88  thf('121', plain,
% 0.64/0.88      (![X6 : $i]:
% 0.64/0.88         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.64/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.64/0.88  thf('122', plain,
% 0.64/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.64/0.88         (~ (m1_pre_topc @ X17 @ X18)
% 0.64/0.88          | ((X19) != (u1_struct_0 @ X17))
% 0.64/0.88          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.64/0.88          | ~ (m1_pre_topc @ X17 @ X18)
% 0.64/0.88          | (v3_pre_topc @ X19 @ X18)
% 0.64/0.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.64/0.88          | ~ (l1_pre_topc @ X18)
% 0.64/0.88          | ~ (v2_pre_topc @ X18))),
% 0.64/0.88      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.64/0.88  thf('123', plain,
% 0.64/0.88      (![X17 : $i, X18 : $i]:
% 0.64/0.88         (~ (v2_pre_topc @ X18)
% 0.64/0.88          | ~ (l1_pre_topc @ X18)
% 0.64/0.88          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.64/0.88               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.64/0.88          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.64/0.88          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.64/0.88          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.64/0.88      inference('simplify', [status(thm)], ['122'])).
% 0.64/0.88  thf('124', plain,
% 0.64/0.88      (![X0 : $i, X1 : $i]:
% 0.64/0.88         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.64/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.64/0.88          | ~ (l1_struct_0 @ X0)
% 0.64/0.88          | ~ (m1_pre_topc @ X0 @ X1)
% 0.64/0.88          | ~ (v1_tsep_1 @ X0 @ X1)
% 0.64/0.88          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X1)
% 0.64/0.88          | ~ (l1_pre_topc @ X1)
% 0.64/0.88          | ~ (v2_pre_topc @ X1))),
% 0.64/0.88      inference('sup-', [status(thm)], ['121', '123'])).
% 0.64/0.88  thf('125', plain,
% 0.64/0.88      (((~ (v2_pre_topc @ sk_A)
% 0.64/0.88         | ~ (l1_pre_topc @ sk_A)
% 0.64/0.88         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.64/0.88         | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.64/0.88         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.64/0.88         | ~ (l1_struct_0 @ sk_C))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('sup-', [status(thm)], ['120', '124'])).
% 0.64/0.88  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('128', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['72', '73'])).
% 0.64/0.88  thf('129', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.64/0.88  thf('130', plain, ((l1_struct_0 @ sk_C)),
% 0.64/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.64/0.88  thf('131', plain,
% 0.64/0.88      ((((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)
% 0.64/0.88         | ~ (v1_tsep_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)],
% 0.64/0.88                ['125', '126', '127', '128', '129', '130'])).
% 0.64/0.88  thf('132', plain,
% 0.64/0.88      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A))
% 0.64/0.88         <= (((v1_tsep_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('sup-', [status(thm)], ['119', '131'])).
% 0.64/0.88  thf('133', plain,
% 0.64/0.88      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.64/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.64/0.88         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['3', '4', '63'])).
% 0.64/0.88  thf('134', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['57', '62'])).
% 0.64/0.88  thf('135', plain,
% 0.64/0.88      (![X17 : $i, X18 : $i]:
% 0.64/0.88         (~ (v2_pre_topc @ X18)
% 0.64/0.88          | ~ (l1_pre_topc @ X18)
% 0.64/0.88          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.64/0.88               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.64/0.88          | (v1_tsep_1 @ X17 @ X18)
% 0.64/0.88          | ~ (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.64/0.88          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.64/0.88      inference('simplify', [status(thm)], ['66'])).
% 0.64/0.88  thf('136', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.64/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.64/0.88          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.64/0.88          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.64/0.88          | (v1_tsep_1 @ sk_B @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | ~ (v2_pre_topc @ X0))),
% 0.64/0.88      inference('sup-', [status(thm)], ['134', '135'])).
% 0.64/0.88  thf('137', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['57', '62'])).
% 0.64/0.88  thf('138', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.64/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.64/0.88          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.64/0.88          | ~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ X0)
% 0.64/0.88          | (v1_tsep_1 @ sk_B @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | ~ (v2_pre_topc @ X0))),
% 0.64/0.88      inference('demod', [status(thm)], ['136', '137'])).
% 0.64/0.88  thf('139', plain,
% 0.64/0.88      (((~ (v2_pre_topc @ sk_A)
% 0.64/0.88         | ~ (l1_pre_topc @ sk_A)
% 0.64/0.88         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.64/0.88         | ~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)
% 0.64/0.88         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('sup-', [status(thm)], ['133', '138'])).
% 0.64/0.88  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('142', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['0'])).
% 0.64/0.88  thf('143', plain,
% 0.64/0.88      ((((v1_tsep_1 @ sk_B @ sk_A)
% 0.64/0.88         | ~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)))
% 0.64/0.88         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.64/0.88  thf('144', plain,
% 0.64/0.88      (((v1_tsep_1 @ sk_B @ sk_A))
% 0.64/0.88         <= (((v1_tsep_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('sup-', [status(thm)], ['132', '143'])).
% 0.64/0.88  thf('145', plain,
% 0.64/0.88      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['108'])).
% 0.64/0.88  thf('146', plain,
% 0.64/0.88      (((v1_tsep_1 @ sk_B @ sk_A)) | ~ ((v1_tsep_1 @ sk_C @ sk_A)) | 
% 0.64/0.88       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.64/0.88      inference('sup-', [status(thm)], ['144', '145'])).
% 0.64/0.88  thf('147', plain, (~ ((v1_tsep_1 @ sk_C @ sk_A))),
% 0.64/0.88      inference('sat_resolution*', [status(thm)],
% 0.64/0.88                ['116', '117', '84', '110', '146'])).
% 0.64/0.88  thf('148', plain, (~ (v1_tsep_1 @ sk_C @ sk_A)),
% 0.64/0.88      inference('simpl_trail', [status(thm)], ['113', '147'])).
% 0.64/0.88  thf('149', plain, (~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)),
% 0.64/0.88      inference('clc', [status(thm)], ['112', '148'])).
% 0.64/0.88  thf('150', plain,
% 0.64/0.88      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.64/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.64/0.88         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('demod', [status(thm)], ['3', '4', '63'])).
% 0.64/0.88  thf('151', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.64/0.88      inference('sat_resolution*', [status(thm)], ['84', '110'])).
% 0.64/0.88  thf('152', plain,
% 0.64/0.88      ((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.64/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.88      inference('simpl_trail', [status(thm)], ['150', '151'])).
% 0.64/0.88  thf('153', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['57', '62'])).
% 0.64/0.88  thf('154', plain,
% 0.64/0.88      (![X17 : $i, X18 : $i]:
% 0.64/0.88         (~ (v2_pre_topc @ X18)
% 0.64/0.88          | ~ (l1_pre_topc @ X18)
% 0.64/0.88          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.64/0.88               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.64/0.88          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.64/0.88          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.64/0.88          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.64/0.88      inference('simplify', [status(thm)], ['122'])).
% 0.64/0.88  thf('155', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.64/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.64/0.88          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.64/0.88          | ~ (v1_tsep_1 @ sk_B @ X0)
% 0.64/0.88          | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | ~ (v2_pre_topc @ X0))),
% 0.64/0.88      inference('sup-', [status(thm)], ['153', '154'])).
% 0.64/0.88  thf('156', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_C))),
% 0.64/0.88      inference('demod', [status(thm)], ['57', '62'])).
% 0.64/0.88  thf('157', plain,
% 0.64/0.88      (![X0 : $i]:
% 0.64/0.88         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.64/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.64/0.88          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.64/0.88          | ~ (v1_tsep_1 @ sk_B @ X0)
% 0.64/0.88          | (v3_pre_topc @ (k2_struct_0 @ sk_C) @ X0)
% 0.64/0.88          | ~ (l1_pre_topc @ X0)
% 0.64/0.88          | ~ (v2_pre_topc @ X0))),
% 0.64/0.88      inference('demod', [status(thm)], ['155', '156'])).
% 0.64/0.88  thf('158', plain,
% 0.64/0.88      ((~ (v2_pre_topc @ sk_A)
% 0.64/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.64/0.88        | (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)
% 0.64/0.88        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.64/0.88        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.64/0.88      inference('sup-', [status(thm)], ['152', '157'])).
% 0.64/0.88  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.88  thf('161', plain,
% 0.64/0.88      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['118'])).
% 0.64/0.88  thf('162', plain,
% 0.64/0.88      (((v1_tsep_1 @ sk_B @ sk_A)) | ((v1_tsep_1 @ sk_C @ sk_A))),
% 0.64/0.88      inference('split', [status(esa)], ['118'])).
% 0.64/0.88  thf('163', plain, (((v1_tsep_1 @ sk_B @ sk_A))),
% 0.64/0.88      inference('sat_resolution*', [status(thm)],
% 0.64/0.88                ['116', '117', '84', '110', '146', '162'])).
% 0.64/0.88  thf('164', plain, ((v1_tsep_1 @ sk_B @ sk_A)),
% 0.64/0.88      inference('simpl_trail', [status(thm)], ['161', '163'])).
% 0.64/0.88  thf('165', plain,
% 0.64/0.88      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.64/0.88      inference('split', [status(esa)], ['0'])).
% 0.64/0.88  thf('166', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.64/0.88      inference('sat_resolution*', [status(thm)], ['84', '110'])).
% 0.64/0.88  thf('167', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.64/0.88      inference('simpl_trail', [status(thm)], ['165', '166'])).
% 0.64/0.88  thf('168', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)),
% 0.64/0.88      inference('demod', [status(thm)], ['158', '159', '160', '164', '167'])).
% 0.64/0.88  thf('169', plain, ($false), inference('demod', [status(thm)], ['149', '168'])).
% 0.64/0.88  
% 0.64/0.88  % SZS output end Refutation
% 0.64/0.88  
% 0.64/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
