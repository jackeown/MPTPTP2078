%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W9Z8WyJ7gz

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 819 expanded)
%              Number of leaves         :   22 ( 229 expanded)
%              Depth                    :   18
%              Number of atoms          : 1216 (14878 expanded)
%              Number of equality atoms :   33 ( 496 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
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

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( X8
       != ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X10 )
      | ( m1_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) @ X10 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14','15','16'])).

thf('18',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('36',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('41',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_pre_topc @ sk_C )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('46',plain,(
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

thf('47',plain,(
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

thf('48',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_pre_topc @ X4 @ X5 )
       != ( g1_pre_topc @ X2 @ X3 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( v1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( v1_pre_topc @ sk_C )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','56'])).

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

thf('58',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v3_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v1_tsep_1 @ sk_B @ X0 )
        | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v1_tsep_1 @ sk_B @ X0 )
        | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('67',plain,
    ( ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','67'])).

thf('69',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('71',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v3_pre_topc @ X13 @ X12 )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','80'])).

thf('82',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','22','31','83'])).

thf('85',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('87',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','22','31'])).

thf('88',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf('90',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ X0 )
        | ( v1_tsep_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
        | ( v1_tsep_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','22'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v1_tsep_1 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
   <= ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('100',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('101',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('102',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v1_tsep_1 @ sk_C @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','106'])).

thf('108',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('109',plain,(
    v1_tsep_1 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','4','22','31','83','108'])).

thf('110',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','22','31'])).

thf('111',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['107','109','110'])).

thf('112',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('113',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','22'])).

thf('114',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['112','113'])).

thf('115',plain,(
    v1_tsep_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['96','97','98','111','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['85','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W9Z8WyJ7gz
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 198 iterations in 0.099s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(t14_tmap_1, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.20/0.56               ( ( ( C ) =
% 0.20/0.56                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.20/0.56                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.56                   ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.56              ( ![C:$i]:
% 0.20/0.56                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.20/0.56                  ( ( ( C ) =
% 0.20/0.56                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.20/0.56                    ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.56                      ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t14_tmap_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.56        | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.20/0.56        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.56        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | ~ ((v1_tsep_1 @ sk_C @ sk_A)) | 
% 0.20/0.56       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('split', [status(esa)], ['3'])).
% 0.20/0.56  thf('5', plain, (((m1_pre_topc @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t12_tmap_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.20/0.56               ( ( ( B ) =
% 0.20/0.56                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.20/0.56                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X8)
% 0.20/0.56          | ~ (l1_pre_topc @ X8)
% 0.20/0.56          | ((X8) != (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.20/0.56          | ~ (m1_pre_topc @ X8 @ X10)
% 0.20/0.56          | (m1_pre_topc @ X9 @ X10)
% 0.20/0.56          | ~ (l1_pre_topc @ X9)
% 0.20/0.56          | ~ (v2_pre_topc @ X9)
% 0.20/0.56          | ~ (l1_pre_topc @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X10)
% 0.20/0.56          | ~ (v2_pre_topc @ X9)
% 0.20/0.56          | ~ (l1_pre_topc @ X9)
% 0.20/0.56          | (m1_pre_topc @ X9 @ X10)
% 0.20/0.56          | ~ (m1_pre_topc @ 
% 0.20/0.56               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)) @ X10)
% 0.20/0.56          | ~ (l1_pre_topc @ 
% 0.20/0.56               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.20/0.56          | ~ (v2_pre_topc @ 
% 0.20/0.56               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_C)
% 0.20/0.56          | ~ (v2_pre_topc @ 
% 0.20/0.56               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.56          | ~ (m1_pre_topc @ 
% 0.20/0.56               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.20/0.56          | (m1_pre_topc @ sk_B @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.56  thf('11', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('13', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('16', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.56          | (m1_pre_topc @ sk_B @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('demod', [status(thm)],
% 0.20/0.56                ['10', '11', '12', '13', '14', '15', '16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['6', '17'])).
% 0.20/0.56  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.56  thf('23', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['23'])).
% 0.20/0.56  thf(t11_tmap_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.56           ( ( v1_pre_topc @
% 0.20/0.56               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.56             ( m1_pre_topc @
% 0.20/0.56               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.56          | (m1_pre_topc @ 
% 0.20/0.56             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)) @ X7)
% 0.20/0.56          | ~ (l1_pre_topc @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.56         | (m1_pre_topc @ 
% 0.20/0.56            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('32', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['32'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.56  thf(t1_tsep_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.56           ( m1_subset_1 @
% 0.20/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.56          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.56          | ~ (l1_pre_topc @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.56         | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.56  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['23'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.56          | (v1_pre_topc @ 
% 0.20/0.56             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.20/0.56          | ~ (l1_pre_topc @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.56         | (v1_pre_topc @ 
% 0.20/0.56            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.56  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('44', plain, (((v1_pre_topc @ sk_C)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ( v1_pre_topc @ A ) =>
% 0.20/0.56         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_pre_topc @ X0)
% 0.20/0.56          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.56  thf(dt_u1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( m1_subset_1 @
% 0.20/0.56         ( u1_pre_topc @ A ) @ 
% 0.20/0.56         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X1 : $i]:
% 0.20/0.56         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.56          | ~ (l1_pre_topc @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.56  thf(free_g1_pre_topc, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.56       ( ![C:$i,D:$i]:
% 0.20/0.56         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.20/0.56           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.56         (((g1_pre_topc @ X4 @ X5) != (g1_pre_topc @ X2 @ X3))
% 0.20/0.56          | ((X4) = (X2))
% 0.20/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.20/0.56      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.56          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.56              != (g1_pre_topc @ X1 @ X2)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v1_pre_topc @ X0)
% 0.20/0.56          | ((u1_struct_0 @ X0) = (X2))
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['46', '49'])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i]:
% 0.20/0.56         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.20/0.56          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.20/0.56          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      ((~ (v1_pre_topc @ sk_C)
% 0.20/0.56        | ~ (l1_pre_topc @ 
% 0.20/0.56             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.56        | ((u1_struct_0 @ 
% 0.20/0.56            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.56            = (u1_struct_0 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '51'])).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('54', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      ((~ (v1_pre_topc @ sk_C) | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      ((((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '56'])).
% 0.20/0.56  thf(t16_tsep_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.56                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.56                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.56          | ((X13) != (u1_struct_0 @ X11))
% 0.20/0.56          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.20/0.56          | ~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.56          | (v3_pre_topc @ X13 @ X12)
% 0.20/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.56          | ~ (l1_pre_topc @ X12)
% 0.20/0.56          | ~ (v2_pre_topc @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X12)
% 0.20/0.56          | ~ (l1_pre_topc @ X12)
% 0.20/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.20/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.56          | (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.20/0.56          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.20/0.56          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.20/0.56      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56              (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.56           | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.56           | ~ (v1_tsep_1 @ sk_B @ X0)
% 0.20/0.56           | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.20/0.56           | ~ (l1_pre_topc @ X0)
% 0.20/0.56           | ~ (v2_pre_topc @ X0)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['57', '59'])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      ((((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '56'])).
% 0.20/0.56  thf('62', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56              (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.56           | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.56           | ~ (v1_tsep_1 @ sk_B @ X0)
% 0.20/0.56           | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.20/0.56           | ~ (l1_pre_topc @ X0)
% 0.20/0.56           | ~ (v2_pre_topc @ X0)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      (((~ (v2_pre_topc @ sk_A)
% 0.20/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.56         | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.56         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '62'])).
% 0.20/0.56  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('66', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['23'])).
% 0.20/0.56  thf('67', plain,
% 0.20/0.56      ((((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.56         | ~ (v1_tsep_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.20/0.56  thf('68', plain,
% 0.20/0.56      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.20/0.56         <= (((v1_tsep_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['33', '67'])).
% 0.20/0.56  thf('69', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['5'])).
% 0.20/0.56  thf('70', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.56          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.56          | ~ (l1_pre_topc @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.56  thf('71', plain,
% 0.20/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.56         | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.56         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.56  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.56  thf('74', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.56          | ((X13) != (u1_struct_0 @ X11))
% 0.20/0.56          | ~ (v3_pre_topc @ X13 @ X12)
% 0.20/0.56          | (v1_tsep_1 @ X11 @ X12)
% 0.20/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.56          | ~ (l1_pre_topc @ X12)
% 0.20/0.56          | ~ (v2_pre_topc @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.56  thf('75', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X12)
% 0.20/0.56          | ~ (l1_pre_topc @ X12)
% 0.20/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.20/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.56          | (v1_tsep_1 @ X11 @ X12)
% 0.20/0.56          | ~ (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.20/0.56          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.20/0.56      inference('simplify', [status(thm)], ['74'])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.56         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.56         | (v1_tsep_1 @ sk_C @ sk_A)
% 0.20/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['73', '75'])).
% 0.20/0.56  thf('77', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['5'])).
% 0.20/0.56  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('80', plain,
% 0.20/0.56      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.56         | (v1_tsep_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.20/0.56  thf('81', plain,
% 0.20/0.56      (((v1_tsep_1 @ sk_C @ sk_A))
% 0.20/0.56         <= (((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.20/0.56             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.20/0.56             ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['68', '80'])).
% 0.20/0.56  thf('82', plain,
% 0.20/0.56      ((~ (v1_tsep_1 @ sk_C @ sk_A)) <= (~ ((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      (((v1_tsep_1 @ sk_C @ sk_A)) | ~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.56       ~ ((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.56  thf('84', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['2', '4', '22', '31', '83'])).
% 0.20/0.56  thf('85', plain, (~ (v1_tsep_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['1', '84'])).
% 0.20/0.56  thf('86', plain,
% 0.20/0.56      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.56  thf('87', plain, (((m1_pre_topc @ sk_C @ sk_A))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['4', '22', '31'])).
% 0.20/0.56  thf('88', plain,
% 0.20/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['86', '87'])).
% 0.20/0.56  thf('89', plain,
% 0.20/0.56      ((((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '56'])).
% 0.20/0.56  thf('90', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X12)
% 0.20/0.56          | ~ (l1_pre_topc @ X12)
% 0.20/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.20/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.56          | (v1_tsep_1 @ X11 @ X12)
% 0.20/0.56          | ~ (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.20/0.56          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.20/0.56      inference('simplify', [status(thm)], ['74'])).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56              (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.56           | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.56           | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ X0)
% 0.20/0.56           | (v1_tsep_1 @ sk_B @ X0)
% 0.20/0.56           | ~ (l1_pre_topc @ X0)
% 0.20/0.56           | ~ (v2_pre_topc @ X0)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.56  thf('92', plain,
% 0.20/0.56      ((((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '56'])).
% 0.20/0.56  thf('93', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56              (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.56           | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.56           | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.20/0.56           | (v1_tsep_1 @ sk_B @ X0)
% 0.20/0.56           | ~ (l1_pre_topc @ X0)
% 0.20/0.56           | ~ (v2_pre_topc @ X0)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.56  thf('94', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['4', '22'])).
% 0.20/0.56  thf('95', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.56          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.56          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.20/0.56          | (v1_tsep_1 @ sk_B @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v2_pre_topc @ X0))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['93', '94'])).
% 0.20/0.56  thf('96', plain,
% 0.20/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.56        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['88', '95'])).
% 0.20/0.56  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('99', plain,
% 0.20/0.56      (((v1_tsep_1 @ sk_C @ sk_A)) <= (((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['32'])).
% 0.20/0.56  thf('100', plain,
% 0.20/0.56      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.56  thf('101', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X12)
% 0.20/0.56          | ~ (l1_pre_topc @ X12)
% 0.20/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.20/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.56          | (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.20/0.56          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.20/0.56          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.20/0.56      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.56  thf('102', plain,
% 0.20/0.56      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.56         | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.20/0.56         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.56  thf('103', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['5'])).
% 0.20/0.56  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('106', plain,
% 0.20/0.56      (((~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.20/0.56         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.20/0.56         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 0.20/0.56  thf('107', plain,
% 0.20/0.56      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.20/0.56         <= (((v1_tsep_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['99', '106'])).
% 0.20/0.56  thf('108', plain,
% 0.20/0.56      (((v1_tsep_1 @ sk_C @ sk_A)) | ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('split', [status(esa)], ['32'])).
% 0.20/0.56  thf('109', plain, (((v1_tsep_1 @ sk_C @ sk_A))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)],
% 0.20/0.56                ['2', '4', '22', '31', '83', '108'])).
% 0.20/0.56  thf('110', plain, (((m1_pre_topc @ sk_C @ sk_A))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['4', '22', '31'])).
% 0.20/0.56  thf('111', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['107', '109', '110'])).
% 0.20/0.56  thf('112', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['23'])).
% 0.20/0.56  thf('113', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['4', '22'])).
% 0.20/0.56  thf('114', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['112', '113'])).
% 0.20/0.56  thf('115', plain, ((v1_tsep_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['96', '97', '98', '111', '114'])).
% 0.20/0.56  thf('116', plain, ($false), inference('demod', [status(thm)], ['85', '115'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
