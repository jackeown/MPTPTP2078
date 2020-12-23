%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1109+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ykS287hItT

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:03 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  264 (28301 expanded)
%              Number of leaves         :   29 (8166 expanded)
%              Depth                    :   46
%              Number of atoms          : 2586 (417693 expanded)
%              Number of equality atoms :  147 (28322 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t31_pre_topc,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                     => ( m1_pre_topc @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_pre_topc])).

thf('2',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('14',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('15',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('16',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( g1_pre_topc @ X17 @ X18 )
       != ( g1_pre_topc @ X15 @ X16 ) )
      | ( X18 = X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_C_1 )
        = X0 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_C_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
     != ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( ( u1_pre_topc @ sk_C_1 )
      = ( u1_pre_topc @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,
    ( ( u1_pre_topc @ sk_C_1 )
    = ( u1_pre_topc @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','24'])).

thf('26',plain,
    ( ( u1_pre_topc @ sk_C_1 )
    = ( u1_pre_topc @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('27',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('28',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) ) )
    | ~ ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( g1_pre_topc @ X17 @ X18 )
       != ( g1_pre_topc @ X15 @ X16 ) )
      | ( X17 = X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_D_2 )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_C_1 ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('35',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('37',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( u1_pre_topc @ sk_C_1 )
    = ( u1_pre_topc @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('39',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_D_2 )
        = X0 )
      | ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
     != ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( ( u1_struct_0 @ sk_D_2 )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['25','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_D_2 )
        = X0 )
      | ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('47',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
     != ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( ( u1_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['44','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('51',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_struct_0 @ sk_D_2 )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['43','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('54',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( u1_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('69',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('75',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('76',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_A )
        = X0 )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_A )
        = X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('84',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( g1_pre_topc @ X17 @ X18 )
       != ( g1_pre_topc @ X15 @ X16 ) )
      | ( X17 = X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('91',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('93',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['81'])).

thf('95',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['88','95'])).

thf('97',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','96'])).

thf('98',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('101',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('104',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

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

thf('105',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X6 ) @ ( k2_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( sk_C @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( m1_pre_topc @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','108'])).

thf('110',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( r1_tarski @ ( k2_struct_0 @ X6 ) @ ( k2_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('112',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( u1_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','54'])).

thf('118',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ( m1_pre_topc @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['109','115','116','117'])).

thf('119',plain,(
    ~ ( m1_pre_topc @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( u1_pre_topc @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X8 @ X6 @ X7 ) @ X8 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X1 @ X0 @ X2 ) @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ X0 ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ X0 ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('129',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('130',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X6 ) @ ( k2_struct_0 @ X7 ) )
      | ( zip_tseitin_0 @ ( sk_D @ X6 @ X7 ) @ ( sk_C @ X6 @ X7 ) @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ ( u1_pre_topc @ X6 ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_D_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_D_2 @ X0 ) @ ( u1_pre_topc @ sk_D_2 ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ X0 ) @ ( sk_C @ sk_D_2 @ X0 ) @ sk_D_2 @ X0 )
      | ~ ( l1_pre_topc @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( u1_pre_topc @ sk_C_1 )
    = ( u1_pre_topc @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('133',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_D_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_D_2 @ X0 ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ X0 ) @ ( sk_C @ sk_D_2 @ X0 ) @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( m1_pre_topc @ sk_D_2 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('137',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( m1_pre_topc @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ~ ( m1_pre_topc @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
        = ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ X2 @ ( k2_struct_0 @ X1 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('142',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( ( sk_C @ sk_D_2 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_D_2 ) @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( u1_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','54'])).

thf('144',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('145',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( ( sk_C @ sk_D_2 @ sk_B )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('147',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('148',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('150',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('151',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('153',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['81'])).

thf('154',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['88','95'])).

thf('156',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( g1_pre_topc @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('159',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['151','159'])).

thf('161',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('162',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('163',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X5 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X5 ) )
      | ( X3
       != ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ X2 @ ( k2_struct_0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('165',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X5 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( zip_tseitin_0 @ X2 @ ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ X2 @ ( k2_struct_0 @ X1 ) ) @ X1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_0 @ X0 @ ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 @ ( k2_struct_0 @ X1 ) ) @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['163','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','166'])).

thf('168',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('169',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( u1_pre_topc @ X4 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('170',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['81'])).

thf('172',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['167','172'])).

thf('174',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k9_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( sk_D @ sk_D_2 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['148','173'])).

thf('175',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['145','174'])).

thf('176',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( zip_tseitin_0 @ ( sk_D @ sk_D_2 @ sk_B ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    m1_subset_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('179',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X6 @ X7 )
      | ( r2_hidden @ X8 @ ( u1_pre_topc @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['177','180'])).

thf('182',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ X0 ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['127','189'])).

thf('191',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','190'])).

thf('192',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('195',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('197',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['97'])).

thf('199',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X5 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( zip_tseitin_0 @ X2 @ ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ X2 @ ( k2_struct_0 @ X1 ) ) @ X1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_0 @ X0 @ ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 @ ( k2_struct_0 @ X1 ) ) @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B ) ),
    inference(simplify,[status(thm)],['81'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_0 @ X0 @ ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 @ ( k2_struct_0 @ X1 ) ) @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_0 @ X0 @ ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 @ ( k2_struct_0 @ X1 ) ) @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['197','204'])).

thf('206',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['191','192'])).

thf('207',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( u1_pre_topc @ X4 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('208',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['205','208'])).

thf('210',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k9_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ sk_D_2 ) ) @ sk_D_2 @ sk_B ),
    inference('sup+',[status(thm)],['55','209'])).

thf('211',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('212',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['191','192'])).

thf('213',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
        = ( k9_subset_1 @ ( u1_struct_0 @ X1 ) @ X2 @ ( k2_struct_0 @ X1 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('214',plain,
    ( ( sk_C @ sk_D_2 @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('216',plain,
    ( ( sk_C @ sk_D_2 @ sk_B )
    = ( k9_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['210','211','216'])).

thf('218',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('219',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('220',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X6 ) @ ( k2_struct_0 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X10 @ ( sk_C @ X6 @ X7 ) @ X6 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ ( u1_pre_topc @ X6 ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_C @ X0 @ sk_B ) @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_C @ X0 @ sk_B ) @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_D_2 )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_D_2 ) )
      | ( m1_pre_topc @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['218','223'])).

thf('225',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('226',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( u1_pre_topc @ sk_C_1 )
    = ( u1_pre_topc @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ( m1_pre_topc @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,(
    ~ ( m1_pre_topc @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B ) ) ),
    inference(clc,[status(thm)],['228','229'])).

thf('231',plain,(
    r2_hidden @ ( sk_C @ sk_D_2 @ sk_B ) @ ( u1_pre_topc @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['188'])).

thf('232',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_D_2 @ sk_B ) @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    $false ),
    inference('sup-',[status(thm)],['217','232'])).


%------------------------------------------------------------------------------
