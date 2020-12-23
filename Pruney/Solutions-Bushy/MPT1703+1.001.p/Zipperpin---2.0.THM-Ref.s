%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1703+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q846sGbwjU

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:06 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  230 (14787 expanded)
%              Number of leaves         :   33 (4305 expanded)
%              Depth                    :   36
%              Number of atoms          : 2164 (197441 expanded)
%              Number of equality atoms :   91 (11005 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( g1_pre_topc @ ( k2_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( g1_pre_topc @ X20 @ X21 )
       != ( g1_pre_topc @ X18 @ X19 ) )
      | ( X21 = X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( v1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      = ( u1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','17','18','19','20'])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('23',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( g1_pre_topc @ X20 @ X21 )
       != ( g1_pre_topc @ X18 @ X19 ) )
      | ( X20 = X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_C_1 )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','17','18','19','20'])).

thf('30',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_C_1 )
        = X0 )
      | ( sk_B
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ sk_C_1 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','31'])).

thf('33',plain,
    ( ( ( u1_struct_0 @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    v1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('37',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['33','34','35','38'])).

thf('40',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('46',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('51',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('53',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['43','51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['41','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['41','53'])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( r1_tarski @ ( k2_struct_0 @ X7 ) @ ( k2_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_B
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( sk_B
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','17','18','19','20'])).

thf('69',plain,
    ( sk_B
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('71',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( g1_pre_topc @ X20 @ X21 )
       != ( g1_pre_topc @ X18 @ X19 ) )
      | ( X20 = X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ~ ( v1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    v1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('78',plain,
    ( sk_B
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_B
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('81',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X7 ) @ ( k2_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( sk_C @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['33','34','35','38'])).

thf('85',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['33','34','35','38'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_C_1 )
        = X0 )
      | ( sk_B
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ sk_C_1 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('94',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['86','95'])).

thf('97',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('101',plain,(
    ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['43','51'])).

thf('102',plain,(
    ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X7 ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X9 @ X7 @ X8 ) @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X1 @ X0 @ X2 ) @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ X0 ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ X0 ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('113',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X7 ) @ ( k2_struct_0 @ X8 ) )
      | ( zip_tseitin_0 @ ( sk_D @ X7 @ X8 ) @ ( sk_C @ X7 @ X8 ) @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ ( u1_pre_topc @ X7 ) )
      | ( m1_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ X0 ) @ ( sk_C @ sk_C_1 @ X0 ) @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','17','18','19','20'])).

thf('116',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( u1_pre_topc @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ X0 ) @ ( sk_C @ sk_C_1 @ X0 ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( u1_pre_topc @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ X0 ) @ ( sk_C @ sk_C_1 @ X0 ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['111','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('124',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X4
        = ( k9_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 @ ( k2_struct_0 @ X2 ) ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('126',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( sk_D @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['33','34','35','38'])).

thf('128',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['33','34','35','38'])).

thf('130',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('132',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127','132'])).

thf('134',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('135',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('136',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('137',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X2: $i,X3: $i,X4: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X6 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X6 ) )
      | ( X4
       != ( k9_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 @ ( k2_struct_0 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('139',plain,(
    ! [X2: $i,X3: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X6 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( zip_tseitin_0 @ X3 @ ( k9_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 @ ( k2_struct_0 @ X2 ) ) @ X2 @ X6 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['137','139'])).

thf('141',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('142',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( u1_pre_topc @ X5 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('143',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['140','143'])).

thf('145',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( k9_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup+',[status(thm)],['134','144'])).

thf('146',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup+',[status(thm)],['133','145'])).

thf('147',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['99','102'])).

thf('149',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('150',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X7 @ X8 )
      | ( r2_hidden @ X9 @ ( u1_pre_topc @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['147','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['41','53'])).

thf('158',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ X0 ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['110','159'])).

thf('161',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','160'])).

thf('162',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('165',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X2: $i,X3: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X6 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( zip_tseitin_0 @ X3 @ ( k9_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 @ ( k2_struct_0 @ X2 ) ) @ X2 @ X6 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['161','162'])).

thf('169',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( u1_pre_topc @ X5 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('170',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['167','170'])).

thf('172',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( k9_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 @ sk_A ),
    inference('sup+',[status(thm)],['39','171'])).

thf('173',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('174',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['161','162'])).

thf('175',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X4
        = ( k9_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 @ ( k2_struct_0 @ X2 ) ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('176',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('178',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( k9_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_B @ sk_A ) @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['172','173','178'])).

thf('180',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['158'])).

thf('181',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('182',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X7 ) @ ( k2_struct_0 @ X8 ) )
      | ~ ( zip_tseitin_0 @ X11 @ ( sk_C @ X7 @ X8 ) @ X7 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ ( u1_pre_topc @ X7 ) )
      | ( m1_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_C @ sk_C_1 @ X0 ) @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','17','18','19','20'])).

thf('185',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( u1_pre_topc @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_C @ sk_C_1 @ X0 ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( u1_pre_topc @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_C @ sk_C_1 @ X0 ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 @ sk_A )
      | ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['180','188'])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 @ sk_A )
      | ( m1_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('194',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    $false ),
    inference('sup-',[status(thm)],['179','194'])).


%------------------------------------------------------------------------------
