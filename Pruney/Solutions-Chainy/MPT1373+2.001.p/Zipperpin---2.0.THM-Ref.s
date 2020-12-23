%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VBFC8nFvaC

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 854 expanded)
%              Number of leaves         :   28 ( 248 expanded)
%              Depth                    :   20
%              Number of atoms          :  848 (11059 expanded)
%              Number of equality atoms :   23 ( 391 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t28_compts_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( C = D )
                   => ( ( v2_compts_1 @ C @ A )
                    <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( C = D )
                     => ( ( v2_compts_1 @ C @ A )
                      <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_compts_1])).

thf('0',plain,
    ( ~ ( v2_compts_1 @ sk_D_3 @ sk_B )
    | ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_compts_1 @ sk_D_3 @ sk_B )
   <= ~ ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_C_1 = sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_B )
   <= ~ ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( v2_compts_1 @ sk_D_3 @ sk_B )
    | ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( v2_compts_1 @ sk_D_3 @ sk_B )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_compts_1 @ sk_D_3 @ sk_B )
   <= ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    sk_C_1 = sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_B )
   <= ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_C_1 = sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('13',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['13','18'])).

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

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( r1_tarski @ ( k2_struct_0 @ X8 ) @ ( k2_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X2
       != ( k1_pre_topc @ X1 @ X0 ) )
      | ( ( k2_struct_0 @ X2 )
        = X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) @ X1 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X1 @ X0 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) )
      = sk_C_1 )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) @ sk_B )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('30',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('32',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('34',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) )
      = sk_C_1 )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','32','33'])).

thf('35',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['13','18'])).

thf('36',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['13','18'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','36','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) )
               => ( ( v2_compts_1 @ C @ A )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( D = C )
                       => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ ( k2_struct_0 @ X17 ) )
      | ( ( sk_D_2 @ X19 @ X17 )
        = X19 )
      | ( v2_compts_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( ( sk_D_2 @ sk_C_1 @ X0 )
        = sk_C_1 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( ( sk_D_2 @ sk_C_1 @ X0 )
        = sk_C_1 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( sk_D_2 @ sk_C_1 @ sk_B )
      = sk_C_1 )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( sk_D_2 @ sk_C_1 @ sk_B )
      = sk_C_1 )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( ( sk_D_2 @ sk_C_1 @ sk_B )
      = sk_C_1 )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','36','41'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ ( k2_struct_0 @ X17 ) )
      | ~ ( v2_compts_1 @ ( sk_D_2 @ X19 @ X17 ) @ X17 )
      | ( v2_compts_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D_2 @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( v2_compts_1 @ ( sk_D_2 @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( v2_compts_1 @ sk_C_1 @ sk_B )
      | ( v2_compts_1 @ sk_C_1 @ sk_A ) )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('63',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_B )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_A )
    | ~ ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','64'])).

thf('66',plain,(
    ~ ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['4','65'])).

thf('67',plain,(
    ~ ( v2_compts_1 @ sk_C_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['3','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ ( k2_struct_0 @ X17 ) )
      | ~ ( v2_compts_1 @ X19 @ X18 )
      | ( X20 != X19 )
      | ( v2_compts_1 @ X20 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('71',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_compts_1 @ X19 @ X17 )
      | ~ ( v2_compts_1 @ X19 @ X18 )
      | ~ ( r1_tarski @ X19 @ ( k2_struct_0 @ X17 ) )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_A )
   <= ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('74',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_A )
    | ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('75',plain,(
    v2_compts_1 @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','65','74'])).

thf('76',plain,(
    v2_compts_1 @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['73','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ( v2_compts_1 @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['72','76','77'])).

thf('79',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_B )
    | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','36','41'])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_compts_1 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['67','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VBFC8nFvaC
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:18:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 94 iterations in 0.050s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.22/0.50  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(t28_compts_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.50                   ( ( ( C ) = ( D ) ) =>
% 0.22/0.50                     ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( l1_pre_topc @ A ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50                  ( ![D:$i]:
% 0.22/0.50                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.50                      ( ( ( C ) = ( D ) ) =>
% 0.22/0.50                        ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t28_compts_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((~ (v2_compts_1 @ sk_D_3 @ sk_B) | ~ (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((~ (v2_compts_1 @ sk_D_3 @ sk_B)) <= (~ ((v2_compts_1 @ sk_D_3 @ sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain, (((sk_C_1) = (sk_D_3))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((~ (v2_compts_1 @ sk_C_1 @ sk_B)) <= (~ ((v2_compts_1 @ sk_D_3 @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (~ ((v2_compts_1 @ sk_D_3 @ sk_B)) | ~ ((v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (((v2_compts_1 @ sk_D_3 @ sk_B) | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.51      (((v2_compts_1 @ sk_D_3 @ sk_B)) <= (((v2_compts_1 @ sk_D_3 @ sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('7', plain, (((sk_C_1) = (sk_D_3))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (((v2_compts_1 @ sk_C_1 @ sk_B)) <= (((v2_compts_1 @ sk_D_3 @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('10', plain, (((sk_C_1) = (sk_D_3))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf(dt_k1_pre_topc, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.51       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.22/0.51         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X13)
% 0.22/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.51          | (m1_pre_topc @ (k1_pre_topc @ X13 @ X14) @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (((m1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1) @ sk_B)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_m1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X15 @ X16)
% 0.22/0.51          | (l1_pre_topc @ X15)
% 0.22/0.51          | ~ (l1_pre_topc @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['13', '18'])).
% 0.22/0.51  thf(d9_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( l1_pre_topc @ B ) =>
% 0.22/0.51           ( ( m1_pre_topc @ B @ A ) <=>
% 0.22/0.51             ( ( ![C:$i]:
% 0.22/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.22/0.51                     ( ?[D:$i]:
% 0.22/0.51                       ( ( m1_subset_1 @
% 0.22/0.51                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.22/0.51                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.22/0.51                         ( ( C ) =
% 0.22/0.51                           ( k9_subset_1 @
% 0.22/0.51                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.22/0.51               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_2, axiom,
% 0.22/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.22/0.51       ( ( ( C ) =
% 0.22/0.51           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.22/0.51         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.22/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_3, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( l1_pre_topc @ B ) =>
% 0.22/0.51           ( ( m1_pre_topc @ B @ A ) <=>
% 0.22/0.51             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.22/0.51               ( ![C:$i]:
% 0.22/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.22/0.51                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X8)
% 0.22/0.51          | ~ (m1_pre_topc @ X8 @ X9)
% 0.22/0.51          | (r1_tarski @ (k2_struct_0 @ X8) @ (k2_struct_0 @ X9))
% 0.22/0.51          | ~ (l1_pre_topc @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.51        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) @ 
% 0.22/0.51           (k2_struct_0 @ sk_B))
% 0.22/0.51        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) @ 
% 0.22/0.51         (k2_struct_0 @ sk_B))
% 0.22/0.51        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1)))),
% 0.22/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf(d10_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.51               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.22/0.51                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.22/0.51          | ((X2) != (k1_pre_topc @ X1 @ X0))
% 0.22/0.51          | ((k2_struct_0 @ X2) = (X0))
% 0.22/0.51          | ~ (m1_pre_topc @ X2 @ X1)
% 0.22/0.51          | ~ (v1_pre_topc @ X2)
% 0.22/0.51          | ~ (l1_pre_topc @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X1)
% 0.22/0.51          | ~ (v1_pre_topc @ (k1_pre_topc @ X1 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ (k1_pre_topc @ X1 @ X0) @ X1)
% 0.22/0.51          | ((k2_struct_0 @ (k1_pre_topc @ X1 @ X0)) = (X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.22/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      ((((k2_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) = (sk_C_1))
% 0.22/0.51        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1) @ sk_B)
% 0.22/0.51        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1))
% 0.22/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['24', '26'])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X13)
% 0.22/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.51          | (v1_pre_topc @ (k1_pre_topc @ X13 @ X14)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (((v1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1)) | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('32', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.51  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      ((((k2_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) = (sk_C_1))
% 0.22/0.51        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1) @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['27', '32', '33'])).
% 0.22/0.51  thf('35', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['13', '18'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (((k2_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) = (sk_C_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.51  thf('37', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['13', '18'])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X15 @ X16)
% 0.22/0.51          | (l1_pre_topc @ X15)
% 0.22/0.51          | ~ (l1_pre_topc @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.51  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('41', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.51  thf('42', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['23', '36', '41'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t11_compts_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 0.22/0.51                 ( ( v2_compts_1 @ C @ A ) <=>
% 0.22/0.51                   ( ![D:$i]:
% 0.22/0.51                     ( ( m1_subset_1 @
% 0.22/0.51                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X17 @ X18)
% 0.22/0.51          | ~ (r1_tarski @ X19 @ (k2_struct_0 @ X17))
% 0.22/0.51          | ((sk_D_2 @ X19 @ X17) = (X19))
% 0.22/0.51          | (v2_compts_1 @ X19 @ X18)
% 0.22/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.51          | ~ (l1_pre_topc @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.22/0.51          | ((sk_D_2 @ sk_C_1 @ X0) = (sk_C_1))
% 0.22/0.51          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.51  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_compts_1 @ sk_C_1 @ sk_A)
% 0.22/0.51          | ((sk_D_2 @ sk_C_1 @ X0) = (sk_C_1))
% 0.22/0.51          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.22/0.51        | ((sk_D_2 @ sk_C_1 @ sk_B) = (sk_C_1))
% 0.22/0.51        | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['42', '47'])).
% 0.22/0.51  thf('49', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      ((((sk_D_2 @ sk_C_1 @ sk_B) = (sk_C_1)) | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      ((~ (v2_compts_1 @ sk_C_1 @ sk_A)) <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      ((((sk_D_2 @ sk_C_1 @ sk_B) = (sk_C_1)))
% 0.22/0.51         <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.51  thf('53', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['23', '36', '41'])).
% 0.22/0.51  thf('54', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X17 @ X18)
% 0.22/0.51          | ~ (r1_tarski @ X19 @ (k2_struct_0 @ X17))
% 0.22/0.51          | ~ (v2_compts_1 @ (sk_D_2 @ X19 @ X17) @ X17)
% 0.22/0.51          | (v2_compts_1 @ X19 @ X18)
% 0.22/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.51          | ~ (l1_pre_topc @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.22/0.51  thf('56', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.22/0.51          | ~ (v2_compts_1 @ (sk_D_2 @ sk_C_1 @ X0) @ X0)
% 0.22/0.51          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.51  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_compts_1 @ sk_C_1 @ sk_A)
% 0.22/0.51          | ~ (v2_compts_1 @ (sk_D_2 @ sk_C_1 @ X0) @ X0)
% 0.22/0.51          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.51  thf('59', plain,
% 0.22/0.51      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.22/0.51        | ~ (v2_compts_1 @ (sk_D_2 @ sk_C_1 @ sk_B) @ sk_B)
% 0.22/0.51        | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['53', '58'])).
% 0.22/0.51  thf('60', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('61', plain,
% 0.22/0.51      ((~ (v2_compts_1 @ (sk_D_2 @ sk_C_1 @ sk_B) @ sk_B)
% 0.22/0.51        | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['59', '60'])).
% 0.22/0.51  thf('62', plain,
% 0.22/0.51      (((~ (v2_compts_1 @ sk_C_1 @ sk_B) | (v2_compts_1 @ sk_C_1 @ sk_A)))
% 0.22/0.51         <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['52', '61'])).
% 0.22/0.51  thf('63', plain,
% 0.22/0.51      ((~ (v2_compts_1 @ sk_C_1 @ sk_A)) <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      ((~ (v2_compts_1 @ sk_C_1 @ sk_B)) <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.51      inference('clc', [status(thm)], ['62', '63'])).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      (((v2_compts_1 @ sk_C_1 @ sk_A)) | ~ ((v2_compts_1 @ sk_D_3 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '64'])).
% 0.22/0.51  thf('66', plain, (~ ((v2_compts_1 @ sk_D_3 @ sk_B))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['4', '65'])).
% 0.22/0.51  thf('67', plain, (~ (v2_compts_1 @ sk_C_1 @ sk_B)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['3', '66'])).
% 0.22/0.51  thf('68', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('69', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('70', plain,
% 0.22/0.51      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X17 @ X18)
% 0.22/0.51          | ~ (r1_tarski @ X19 @ (k2_struct_0 @ X17))
% 0.22/0.51          | ~ (v2_compts_1 @ X19 @ X18)
% 0.22/0.51          | ((X20) != (X19))
% 0.22/0.51          | (v2_compts_1 @ X20 @ X17)
% 0.22/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.51          | ~ (l1_pre_topc @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.22/0.51  thf('71', plain,
% 0.22/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X18)
% 0.22/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.51          | (v2_compts_1 @ X19 @ X17)
% 0.22/0.51          | ~ (v2_compts_1 @ X19 @ X18)
% 0.22/0.51          | ~ (r1_tarski @ X19 @ (k2_struct_0 @ X17))
% 0.22/0.51          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.22/0.51      inference('simplify', [status(thm)], ['70'])).
% 0.22/0.51  thf('72', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.51          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.22/0.51          | ~ (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.22/0.51          | (v2_compts_1 @ sk_C_1 @ X0)
% 0.22/0.51          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['69', '71'])).
% 0.22/0.51  thf('73', plain,
% 0.22/0.51      (((v2_compts_1 @ sk_C_1 @ sk_A)) <= (((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      (((v2_compts_1 @ sk_C_1 @ sk_A)) | ((v2_compts_1 @ sk_D_3 @ sk_B))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('75', plain, (((v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['4', '65', '74'])).
% 0.22/0.51  thf('76', plain, ((v2_compts_1 @ sk_C_1 @ sk_A)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['73', '75'])).
% 0.22/0.51  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('78', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.51          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.22/0.51          | (v2_compts_1 @ sk_C_1 @ X0)
% 0.22/0.51          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.51      inference('demod', [status(thm)], ['72', '76', '77'])).
% 0.22/0.51  thf('79', plain,
% 0.22/0.51      (((v2_compts_1 @ sk_C_1 @ sk_B)
% 0.22/0.51        | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))
% 0.22/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['68', '78'])).
% 0.22/0.51  thf('80', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['23', '36', '41'])).
% 0.22/0.51  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('82', plain, ((v2_compts_1 @ sk_C_1 @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.22/0.51  thf('83', plain, ($false), inference('demod', [status(thm)], ['67', '82'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
