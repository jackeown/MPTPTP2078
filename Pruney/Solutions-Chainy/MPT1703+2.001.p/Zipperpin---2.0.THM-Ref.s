%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aQZ5VIYTXY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:07 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  102 (1176 expanded)
%              Number of leaves         :   18 ( 346 expanded)
%              Depth                    :   16
%              Number of atoms          :  967 (16267 expanded)
%              Number of equality atoms :   64 (1032 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t12_tmap_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                  <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tmap_1])).

thf('0',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('5',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( l1_pre_topc @ C )
             => ! [D: $i] :
                  ( ( l1_pre_topc @ D )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) )
                      & ( m1_pre_topc @ C @ A ) )
                   => ( m1_pre_topc @ D @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( m1_pre_topc @ X8 @ X7 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != sk_B )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ sk_C @ X2 )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != sk_B )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ sk_C @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != sk_B ) ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != sk_B )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X1 )
      | ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('17',plain,
    ( ( v1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X1 )
      | ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['13','14','20'])).

thf('22',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('31',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
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

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_C )
        = X0 )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_C )
        = X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ sk_C )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( ( ( u1_pre_topc @ sk_C )
      = ( u1_pre_topc @ sk_B ) )
    | ~ ( v1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('42',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['39','40','41'])).

thf('43',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('45',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( v1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    v1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('52',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','42'])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','42'])).

thf('55',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('57',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( m1_pre_topc @ X8 @ X7 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( m1_pre_topc @ X0 @ X3 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(eq_res,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['39','40','41'])).

thf('64',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','42'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('66',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    v1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('69',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['39','40','41'])).

thf('70',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('74',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['39','40','41'])).

thf('75',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','66','67','68','69','70','71','72','73','74','75'])).

thf('77',plain,
    ( ( ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['28','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aQZ5VIYTXY
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:12:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 118 iterations in 0.071s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.34/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.53  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.34/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.53  thf(t12_tmap_1, conjecture,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.34/0.53           ( ![C:$i]:
% 0.34/0.53             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.34/0.53               ( ( ( B ) =
% 0.34/0.53                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.34/0.53                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i]:
% 0.34/0.53        ( ( l1_pre_topc @ A ) =>
% 0.34/0.53          ( ![B:$i]:
% 0.34/0.53            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.34/0.53              ( ![C:$i]:
% 0.34/0.53                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.34/0.53                  ( ( ( B ) =
% 0.34/0.53                      ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.34/0.53                    ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t12_tmap_1])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      ((~ (m1_pre_topc @ sk_C @ sk_A) | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (~ ((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['2'])).
% 0.34/0.53  thf(abstractness_v1_pre_topc, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( ( v1_pre_topc @ A ) =>
% 0.34/0.53         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_pre_topc @ X0)
% 0.34/0.53          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.34/0.53          | ~ (l1_pre_topc @ X0))),
% 0.34/0.53      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t31_pre_topc, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( l1_pre_topc @ B ) =>
% 0.34/0.53           ( ![C:$i]:
% 0.34/0.53             ( ( l1_pre_topc @ C ) =>
% 0.34/0.53               ( ![D:$i]:
% 0.34/0.53                 ( ( l1_pre_topc @ D ) =>
% 0.34/0.53                   ( ( ( ( g1_pre_topc @
% 0.34/0.53                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.34/0.53                         ( g1_pre_topc @
% 0.34/0.53                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.34/0.53                       ( ( g1_pre_topc @
% 0.34/0.53                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.34/0.53                         ( g1_pre_topc @
% 0.34/0.53                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 0.34/0.53                       ( m1_pre_topc @ C @ A ) ) =>
% 0.34/0.53                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ X7)
% 0.34/0.53          | ~ (l1_pre_topc @ X8)
% 0.34/0.53          | (m1_pre_topc @ X8 @ X7)
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))
% 0.34/0.53              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.34/0.53          | ~ (m1_pre_topc @ X9 @ X10)
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 0.34/0.53              != (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.34/0.53          | ~ (l1_pre_topc @ X9)
% 0.34/0.53          | ~ (l1_pre_topc @ X10))),
% 0.34/0.53      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) != (sk_B))
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))
% 0.34/0.53              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.34/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.34/0.53          | (m1_pre_topc @ sk_C @ X2)
% 0.34/0.53          | ~ (l1_pre_topc @ sk_C)
% 0.34/0.53          | ~ (l1_pre_topc @ X2))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.53  thf('8', plain, ((l1_pre_topc @ sk_C)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) != (sk_B))
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))
% 0.34/0.53              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.34/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.34/0.53          | (m1_pre_topc @ sk_C @ X2)
% 0.34/0.53          | ~ (l1_pre_topc @ X2))),
% 0.34/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ X0)
% 0.34/0.53          | (m1_pre_topc @ sk_C @ X0)
% 0.34/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) != (sk_B)))),
% 0.34/0.53      inference('eq_res', [status(thm)], ['9'])).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) != (sk_B))
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.34/0.53          | (m1_pre_topc @ sk_C @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((X0) != (sk_B))
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (v1_pre_topc @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | (m1_pre_topc @ sk_C @ X1)
% 0.34/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['4', '11'])).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X1 : $i]:
% 0.34/0.53         (~ (m1_pre_topc @ sk_B @ X1)
% 0.34/0.53          | (m1_pre_topc @ sk_C @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | ~ (v1_pre_topc @ sk_B)
% 0.34/0.53          | ~ (l1_pre_topc @ sk_B))),
% 0.34/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.34/0.53  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(fc6_pre_topc, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( ( v1_pre_topc @
% 0.34/0.53           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.34/0.53         ( v2_pre_topc @
% 0.34/0.53           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (![X2 : $i]:
% 0.34/0.53         ((v1_pre_topc @ 
% 0.34/0.53           (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.34/0.53          | ~ (l1_pre_topc @ X2)
% 0.34/0.53          | ~ (v2_pre_topc @ X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (((v1_pre_topc @ sk_B) | ~ (v2_pre_topc @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 0.34/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.34/0.53  thf('18', plain, ((v2_pre_topc @ sk_C)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('19', plain, ((l1_pre_topc @ sk_C)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('20', plain, ((v1_pre_topc @ sk_B)),
% 0.34/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (![X1 : $i]:
% 0.34/0.53         (~ (m1_pre_topc @ sk_B @ X1)
% 0.34/0.53          | (m1_pre_topc @ sk_C @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X1))),
% 0.34/0.53      inference('simplify_reflect+', [status(thm)], ['13', '14', '20'])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_C @ sk_A)))
% 0.34/0.53         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['3', '21'])).
% 0.34/0.53  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.34/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      (((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.34/0.53      inference('split', [status(esa)], ['2'])).
% 0.34/0.53  thf('28', plain,
% 0.34/0.53      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['2'])).
% 0.34/0.53  thf('29', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_pre_topc @ X0)
% 0.34/0.53          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.34/0.53          | ~ (l1_pre_topc @ X0))),
% 0.34/0.53      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.34/0.53  thf('31', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(dt_u1_pre_topc, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( m1_subset_1 @
% 0.34/0.53         ( u1_pre_topc @ A ) @ 
% 0.34/0.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.34/0.53  thf('32', plain,
% 0.34/0.53      (![X1 : $i]:
% 0.34/0.53         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.34/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.34/0.53          | ~ (l1_pre_topc @ X1))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.34/0.53  thf(free_g1_pre_topc, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.34/0.53       ( ![C:$i,D:$i]:
% 0.34/0.53         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.34/0.53           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.53         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.34/0.53          | ((X6) = (X4))
% 0.34/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.34/0.53      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ X0)
% 0.34/0.53          | ((u1_pre_topc @ X0) = (X1))
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.34/0.53              != (g1_pre_topc @ X2 @ X1)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((sk_B) != (g1_pre_topc @ X1 @ X0))
% 0.34/0.53          | ((u1_pre_topc @ sk_C) = (X0))
% 0.34/0.53          | ~ (l1_pre_topc @ sk_C))),
% 0.34/0.53      inference('sup-', [status(thm)], ['31', '34'])).
% 0.34/0.53  thf('36', plain, ((l1_pre_topc @ sk_C)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('37', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((sk_B) != (g1_pre_topc @ X1 @ X0)) | ((u1_pre_topc @ sk_C) = (X0)))),
% 0.34/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((sk_B) != (X0))
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (v1_pre_topc @ X0)
% 0.34/0.53          | ((u1_pre_topc @ sk_C) = (u1_pre_topc @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['30', '37'])).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      ((((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))
% 0.34/0.53        | ~ (v1_pre_topc @ sk_B)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.34/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.34/0.53  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('41', plain, ((v1_pre_topc @ sk_B)),
% 0.34/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.34/0.53  thf('42', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.34/0.53      inference('simplify_reflect+', [status(thm)], ['39', '40', '41'])).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['29', '42'])).
% 0.34/0.53  thf('44', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_pre_topc @ X0)
% 0.34/0.53          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.34/0.53          | ~ (l1_pre_topc @ X0))),
% 0.34/0.53      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.34/0.53  thf('45', plain,
% 0.34/0.53      (![X1 : $i]:
% 0.34/0.53         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.34/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.34/0.53          | ~ (l1_pre_topc @ X1))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.34/0.53  thf('46', plain,
% 0.34/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.53         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.34/0.53          | ((X5) = (X3))
% 0.34/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.34/0.53      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.34/0.53  thf('47', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ X0)
% 0.34/0.53          | ((u1_struct_0 @ X0) = (X1))
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.34/0.53              != (g1_pre_topc @ X1 @ X2)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.34/0.53  thf('48', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (v1_pre_topc @ X0)
% 0.34/0.53          | ((u1_struct_0 @ X0) = (X2))
% 0.34/0.53          | ~ (l1_pre_topc @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['44', '47'])).
% 0.34/0.53  thf('49', plain,
% 0.34/0.53      (![X1 : $i, X2 : $i]:
% 0.34/0.53         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.34/0.53          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.34/0.53          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.34/0.53  thf('50', plain,
% 0.34/0.53      ((~ (v1_pre_topc @ sk_B)
% 0.34/0.53        | ~ (l1_pre_topc @ 
% 0.34/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))
% 0.34/0.53        | ((u1_struct_0 @ 
% 0.34/0.53            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))
% 0.34/0.53            = (u1_struct_0 @ sk_C)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['43', '49'])).
% 0.34/0.53  thf('51', plain, ((v1_pre_topc @ sk_B)),
% 0.34/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.34/0.53  thf('52', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['29', '42'])).
% 0.34/0.53  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('54', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['29', '42'])).
% 0.34/0.53  thf('55', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.34/0.53  thf('56', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_pre_topc @ X0)
% 0.34/0.53          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.34/0.53          | ~ (l1_pre_topc @ X0))),
% 0.34/0.53      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.34/0.53  thf('57', plain,
% 0.34/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ X7)
% 0.34/0.53          | ~ (l1_pre_topc @ X8)
% 0.34/0.53          | (m1_pre_topc @ X8 @ X7)
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))
% 0.34/0.53              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.34/0.53          | ~ (m1_pre_topc @ X9 @ X10)
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 0.34/0.53              != (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.34/0.53          | ~ (l1_pre_topc @ X9)
% 0.34/0.53          | ~ (l1_pre_topc @ X10))),
% 0.34/0.53      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.34/0.53  thf('58', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         (((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) != (X0))
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (v1_pre_topc @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X2)
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.34/0.53              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.34/0.53          | ~ (m1_pre_topc @ X1 @ X2)
% 0.34/0.53          | (m1_pre_topc @ X0 @ X3)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X3))),
% 0.34/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.34/0.53  thf('59', plain,
% 0.34/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ X3)
% 0.34/0.53          | (m1_pre_topc @ 
% 0.34/0.53             (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X3)
% 0.34/0.53          | ~ (m1_pre_topc @ X1 @ X2)
% 0.34/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.34/0.53              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X2)
% 0.34/0.53          | ~ (v1_pre_topc @ 
% 0.34/0.53               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.34/0.53          | ~ (l1_pre_topc @ 
% 0.34/0.53               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.34/0.53      inference('simplify', [status(thm)], ['58'])).
% 0.34/0.53  thf('60', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ 
% 0.34/0.53             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.34/0.53          | ~ (v1_pre_topc @ 
% 0.34/0.53               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.34/0.53          | (m1_pre_topc @ 
% 0.34/0.53             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X1))),
% 0.34/0.53      inference('eq_res', [status(thm)], ['59'])).
% 0.34/0.53  thf('61', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((m1_pre_topc @ 
% 0.34/0.53           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.34/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ X1)
% 0.34/0.53          | ~ (v1_pre_topc @ 
% 0.34/0.53               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.34/0.53          | ~ (l1_pre_topc @ 
% 0.34/0.53               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.34/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.34/0.53  thf('62', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_pre_topc @ 
% 0.34/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))
% 0.34/0.53          | ~ (l1_pre_topc @ 
% 0.34/0.53               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.34/0.53          | ~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (l1_pre_topc @ sk_C)
% 0.34/0.53          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.34/0.53          | (m1_pre_topc @ 
% 0.34/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['55', '61'])).
% 0.34/0.53  thf('63', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.34/0.53      inference('simplify_reflect+', [status(thm)], ['39', '40', '41'])).
% 0.34/0.53  thf('64', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['29', '42'])).
% 0.34/0.53  thf('65', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.34/0.53  thf('66', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.34/0.53  thf('67', plain, ((v1_pre_topc @ sk_B)),
% 0.34/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.34/0.53  thf('68', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.34/0.53  thf('69', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.34/0.53      inference('simplify_reflect+', [status(thm)], ['39', '40', '41'])).
% 0.34/0.53  thf('70', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.34/0.53  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('72', plain, ((l1_pre_topc @ sk_C)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('73', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.34/0.53  thf('74', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.34/0.53      inference('simplify_reflect+', [status(thm)], ['39', '40', '41'])).
% 0.34/0.53  thf('75', plain,
% 0.34/0.53      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.34/0.53  thf('76', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (l1_pre_topc @ X0)
% 0.34/0.53          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.34/0.53          | (m1_pre_topc @ sk_B @ X0))),
% 0.34/0.53      inference('demod', [status(thm)],
% 0.34/0.53                ['62', '63', '66', '67', '68', '69', '70', '71', '72', '73', 
% 0.34/0.53                 '74', '75'])).
% 0.34/0.53  thf('77', plain,
% 0.34/0.53      ((((m1_pre_topc @ sk_B @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.34/0.53         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['28', '76'])).
% 0.34/0.53  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('79', plain,
% 0.34/0.53      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.34/0.53      inference('demod', [status(thm)], ['77', '78'])).
% 0.34/0.53  thf('80', plain,
% 0.34/0.53      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('81', plain,
% 0.34/0.53      (~ ((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.34/0.53  thf('82', plain, ($false),
% 0.34/0.53      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '81'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.39/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
