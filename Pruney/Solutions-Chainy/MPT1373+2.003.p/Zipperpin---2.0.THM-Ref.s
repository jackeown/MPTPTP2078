%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I2F3ZxilPd

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 840 expanded)
%              Number of leaves         :   31 ( 249 expanded)
%              Depth                    :   22
%              Number of atoms          :  792 (10314 expanded)
%              Number of equality atoms :   23 ( 366 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X11 @ X12 ) @ X11 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( r1_tarski @ ( k2_struct_0 @ X6 ) @ ( k2_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X17 @ X16 ) )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('27',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) )
      = sk_C_1 )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['13','18'])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('34',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('35',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('36',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('39',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','37','38'])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ( ( sk_D_2 @ X20 @ X18 )
        = X20 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( ( sk_D_2 @ sk_C_1 @ X0 )
        = sk_C_1 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( ( sk_D_2 @ sk_C_1 @ X0 )
        = sk_C_1 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( sk_D_2 @ sk_C_1 @ sk_B )
      = sk_C_1 )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( sk_D_2 @ sk_C_1 @ sk_B )
      = sk_C_1 )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( ( sk_D_2 @ sk_C_1 @ sk_B )
      = sk_C_1 )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','37','38'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( v2_compts_1 @ ( sk_D_2 @ X20 @ X18 ) @ X18 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D_2 @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v2_compts_1 @ ( sk_D_2 @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( v2_compts_1 @ sk_C_1 @ sk_B )
      | ( v2_compts_1 @ sk_C_1 @ sk_A ) )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_B )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_A )
    | ~ ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','61'])).

thf('63',plain,(
    ~ ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['4','62'])).

thf('64',plain,(
    ~ ( v2_compts_1 @ sk_C_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['3','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( v2_compts_1 @ X20 @ X19 )
      | ( X21 != X20 )
      | ( v2_compts_1 @ X21 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('68',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v2_compts_1 @ X20 @ X18 )
      | ~ ( v2_compts_1 @ X20 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_A )
   <= ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('71',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_A )
    | ( v2_compts_1 @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('72',plain,(
    v2_compts_1 @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','62','71'])).

thf('73',plain,(
    v2_compts_1 @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['70','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ( v2_compts_1 @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['69','73','74'])).

thf('76',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_B )
    | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','75'])).

thf('77',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','37','38'])).

thf('78',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_compts_1 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['64','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I2F3ZxilPd
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 166 iterations in 0.103s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.56  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.21/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.56  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.21/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.21/0.56  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.21/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.56  thf(t28_compts_1, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                   ( ( ( C ) = ( D ) ) =>
% 0.21/0.56                     ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( l1_pre_topc @ A ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56                  ( ![D:$i]:
% 0.21/0.56                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                      ( ( ( C ) = ( D ) ) =>
% 0.21/0.56                        ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t28_compts_1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      ((~ (v2_compts_1 @ sk_D_3 @ sk_B) | ~ (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      ((~ (v2_compts_1 @ sk_D_3 @ sk_B)) <= (~ ((v2_compts_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('2', plain, (((sk_C_1) = (sk_D_3))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      ((~ (v2_compts_1 @ sk_C_1 @ sk_B)) <= (~ ((v2_compts_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (~ ((v2_compts_1 @ sk_D_3 @ sk_B)) | ~ ((v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (((v2_compts_1 @ sk_D_3 @ sk_B) | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (((v2_compts_1 @ sk_D_3 @ sk_B)) <= (((v2_compts_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.56      inference('split', [status(esa)], ['5'])).
% 0.21/0.56  thf('7', plain, (((sk_C_1) = (sk_D_3))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (((v2_compts_1 @ sk_C_1 @ sk_B)) <= (((v2_compts_1 @ sk_D_3 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('10', plain, (((sk_C_1) = (sk_D_3))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf(dt_k1_pre_topc, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.56       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.21/0.56         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X11)
% 0.21/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.56          | (m1_pre_topc @ (k1_pre_topc @ X11 @ X12) @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (((m1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1) @ sk_B)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.56  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(dt_m1_pre_topc, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.56          | (l1_pre_topc @ X14)
% 0.21/0.56          | ~ (l1_pre_topc @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.56  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('19', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1) @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['13', '18'])).
% 0.21/0.56  thf(d9_pre_topc, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( l1_pre_topc @ B ) =>
% 0.21/0.56           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.56             ( ( ![C:$i]:
% 0.21/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.56                     ( ?[D:$i]:
% 0.21/0.56                       ( ( m1_subset_1 @
% 0.21/0.56                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.56                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.56                         ( ( C ) =
% 0.21/0.56                           ( k9_subset_1 @
% 0.21/0.56                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.21/0.56               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_2, axiom,
% 0.21/0.56    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.56     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.56       ( ( ( C ) =
% 0.21/0.56           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.21/0.56         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_3, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( l1_pre_topc @ B ) =>
% 0.21/0.56           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.56             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.21/0.56               ( ![C:$i]:
% 0.21/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.56                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X6)
% 0.21/0.56          | ~ (m1_pre_topc @ X6 @ X7)
% 0.21/0.56          | (r1_tarski @ (k2_struct_0 @ X6) @ (k2_struct_0 @ X7))
% 0.21/0.56          | ~ (l1_pre_topc @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.56        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) @ 
% 0.21/0.56           (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf(t29_pre_topc, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.56          | ((u1_struct_0 @ (k1_pre_topc @ X17 @ X16)) = (X16))
% 0.21/0.56          | ~ (l1_pre_topc @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.56        | ((u1_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) = (sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (((u1_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) = (sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf(d3_struct_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((((k2_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) = (sk_C_1))
% 0.21/0.56        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf('30', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1) @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['13', '18'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.56          | (l1_pre_topc @ X14)
% 0.21/0.56          | ~ (l1_pre_topc @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.56  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('34', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.56  thf(dt_l1_pre_topc, axiom,
% 0.21/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('36', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (((k2_struct_0 @ (k1_pre_topc @ sk_B @ sk_C_1)) = (sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['29', '36'])).
% 0.21/0.56  thf('38', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_B @ sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.56  thf('39', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['21', '22', '37', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t11_compts_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 0.21/0.56                 ( ( v2_compts_1 @ C @ A ) <=>
% 0.21/0.56                   ( ![D:$i]:
% 0.21/0.56                     ( ( m1_subset_1 @
% 0.21/0.56                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.56         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.56          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 0.21/0.56          | ((sk_D_2 @ X20 @ X18) = (X20))
% 0.21/0.56          | (v2_compts_1 @ X20 @ X19)
% 0.21/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.56          | ~ (l1_pre_topc @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.21/0.56          | ((sk_D_2 @ sk_C_1 @ X0) = (sk_C_1))
% 0.21/0.56          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.56  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_compts_1 @ sk_C_1 @ sk_A)
% 0.21/0.56          | ((sk_D_2 @ sk_C_1 @ X0) = (sk_C_1))
% 0.21/0.56          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.57        | ((sk_D_2 @ sk_C_1 @ sk_B) = (sk_C_1))
% 0.21/0.57        | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['39', '44'])).
% 0.21/0.57  thf('46', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      ((((sk_D_2 @ sk_C_1 @ sk_B) = (sk_C_1)) | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ sk_C_1 @ sk_A)) <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      ((((sk_D_2 @ sk_C_1 @ sk_B) = (sk_C_1)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.57  thf('50', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['21', '22', '37', '38'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.57          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 0.21/0.57          | ~ (v2_compts_1 @ (sk_D_2 @ X20 @ X18) @ X18)
% 0.21/0.57          | (v2_compts_1 @ X20 @ X19)
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ sk_A)
% 0.21/0.57          | (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.21/0.57          | ~ (v2_compts_1 @ (sk_D_2 @ sk_C_1 @ X0) @ X0)
% 0.21/0.57          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.21/0.57          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_compts_1 @ sk_C_1 @ sk_A)
% 0.21/0.57          | ~ (v2_compts_1 @ (sk_D_2 @ sk_C_1 @ X0) @ X0)
% 0.21/0.57          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.21/0.57          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.57        | ~ (v2_compts_1 @ (sk_D_2 @ sk_C_1 @ sk_B) @ sk_B)
% 0.21/0.57        | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['50', '55'])).
% 0.21/0.57  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('58', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ (sk_D_2 @ sk_C_1 @ sk_B) @ sk_B)
% 0.21/0.57        | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (((~ (v2_compts_1 @ sk_C_1 @ sk_B) | (v2_compts_1 @ sk_C_1 @ sk_A)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['49', '58'])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ sk_C_1 @ sk_A)) <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ sk_C_1 @ sk_B)) <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.57      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_C_1 @ sk_A)) | ~ ((v2_compts_1 @ sk_D_3 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '61'])).
% 0.21/0.57  thf('63', plain, (~ ((v2_compts_1 @ sk_D_3 @ sk_B))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['4', '62'])).
% 0.21/0.57  thf('64', plain, (~ (v2_compts_1 @ sk_C_1 @ sk_B)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['3', '63'])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.57          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 0.21/0.57          | ~ (v2_compts_1 @ X20 @ X19)
% 0.21/0.57          | ((X21) != (X20))
% 0.21/0.57          | (v2_compts_1 @ X21 @ X18)
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X19)
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.57          | (v2_compts_1 @ X20 @ X18)
% 0.21/0.57          | ~ (v2_compts_1 @ X20 @ X19)
% 0.21/0.57          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 0.21/0.57          | ~ (m1_pre_topc @ X18 @ X19))),
% 0.21/0.57      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.57          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.21/0.57          | ~ (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.21/0.57          | (v2_compts_1 @ sk_C_1 @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.57          | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['66', '68'])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_C_1 @ sk_A)) <= (((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['5'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_C_1 @ sk_A)) | ((v2_compts_1 @ sk_D_3 @ sk_B))),
% 0.21/0.57      inference('split', [status(esa)], ['5'])).
% 0.21/0.57  thf('72', plain, (((v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['4', '62', '71'])).
% 0.21/0.57  thf('73', plain, ((v2_compts_1 @ sk_C_1 @ sk_A)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['70', '72'])).
% 0.21/0.57  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.57          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.21/0.57          | (v2_compts_1 @ sk_C_1 @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.57      inference('demod', [status(thm)], ['69', '73', '74'])).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_C_1 @ sk_B)
% 0.21/0.57        | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['65', '75'])).
% 0.21/0.57  thf('77', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['21', '22', '37', '38'])).
% 0.21/0.57  thf('78', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('79', plain, ((v2_compts_1 @ sk_C_1 @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.21/0.57  thf('80', plain, ($false), inference('demod', [status(thm)], ['64', '79'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
