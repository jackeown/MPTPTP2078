%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1645+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a7VGilLRSh

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 255 expanded)
%              Number of leaves         :   19 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  929 (5472 expanded)
%              Number of equality atoms :   41 ( 272 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_waybel_0_type,type,(
    k3_waybel_0: $i > $i > $i )).

thf(k4_waybel_0_type,type,(
    k4_waybel_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_3_type,type,(
    sk_A_3: $i )).

thf(t25_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( C = D )
                     => ( ( ( v12_waybel_0 @ C @ A )
                         => ( v12_waybel_0 @ D @ B ) )
                        & ( ( v13_waybel_0 @ C @ A )
                         => ( v13_waybel_0 @ D @ B ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( l1_orders_2 @ B )
           => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( C = D )
                       => ( ( ( v12_waybel_0 @ C @ A )
                           => ( v12_waybel_0 @ D @ B ) )
                          & ( ( v13_waybel_0 @ C @ A )
                           => ( v13_waybel_0 @ D @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_waybel_0])).

thf('0',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_A_3 )
    | ( v13_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_A_3 )
    | ( v13_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B_2 )
    | ( v13_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ sk_A_3 )
   <= ( v13_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ( r1_tarski @ ( k4_waybel_0 @ A @ B ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ X20 )
      | ( r1_tarski @ ( k4_waybel_0 @ X20 @ X19 ) @ X19 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t24_waybel_0])).

thf('6',plain,
    ( ~ ( l1_orders_2 @ sk_A_3 )
    | ( r1_tarski @ ( k4_waybel_0 @ sk_A_3 @ sk_C_1 ) @ sk_C_1 )
    | ~ ( v13_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_orders_2 @ sk_A_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tarski @ ( k4_waybel_0 @ sk_A_3 @ sk_C_1 ) @ sk_C_1 )
    | ~ ( v13_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k4_waybel_0 @ sk_A_3 @ sk_C_1 ) @ sk_C_1 )
   <= ( v13_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r1_tarski @ ( k4_waybel_0 @ X20 @ X19 ) @ X19 )
      | ( v13_waybel_0 @ X19 @ X20 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t24_waybel_0])).

thf('14',plain,
    ( ~ ( l1_orders_2 @ sk_B_2 )
    | ( v13_waybel_0 @ sk_C_1 @ sk_B_2 )
    | ~ ( r1_tarski @ ( k4_waybel_0 @ sk_B_2 @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ sk_B_2 )
    | ~ ( r1_tarski @ ( k4_waybel_0 @ sk_B_2 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('18',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A_3 ) @ ( u1_orders_2 @ sk_A_3 ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_orders_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( C = D )
                     => ( ( ( k3_waybel_0 @ A @ C )
                          = ( k3_waybel_0 @ B @ D ) )
                        & ( ( k4_waybel_0 @ A @ C )
                          = ( k4_waybel_0 @ B @ D ) ) ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k4_waybel_0 @ X15 @ X16 )
        = ( k4_waybel_0 @ X13 @ X14 ) )
      | ( X16 != X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X13 ) @ ( u1_orders_2 @ X13 ) ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t13_waybel_0])).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X13 ) @ ( u1_orders_2 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k4_waybel_0 @ X15 @ X14 )
        = ( k4_waybel_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A_3 ) @ ( u1_orders_2 @ sk_A_3 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k4_waybel_0 @ sk_B_2 @ X1 )
        = ( k4_waybel_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ~ ( l1_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A_3 ) @ ( u1_orders_2 @ sk_A_3 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k4_waybel_0 @ sk_B_2 @ X1 )
        = ( k4_waybel_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( ( k4_waybel_0 @ sk_B_2 @ X0 )
        = ( k4_waybel_0 @ sk_A_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) )
      | ~ ( l1_orders_2 @ sk_A_3 ) ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( ( k4_waybel_0 @ sk_B_2 @ X0 )
        = ( k4_waybel_0 @ sk_A_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) )
    | ( ( k4_waybel_0 @ sk_B_2 @ sk_C_1 )
      = ( k4_waybel_0 @ sk_A_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k4_waybel_0 @ sk_B_2 @ sk_C_1 )
    = ( k4_waybel_0 @ sk_A_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ sk_B_2 )
    | ~ ( r1_tarski @ ( k4_waybel_0 @ sk_A_3 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','29'])).

thf('31',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B_2 )
    | ~ ( v13_waybel_0 @ sk_D @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v12_waybel_0 @ sk_C_1 @ sk_B_2 )
    | ~ ( v13_waybel_0 @ sk_C_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( v13_waybel_0 @ sk_C_1 @ sk_B_2 )
   <= ~ ( v13_waybel_0 @ sk_C_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_A_3 )
    | ~ ( v13_waybel_0 @ sk_D @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_A_3 )
    | ~ ( v13_waybel_0 @ sk_C_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_A_3 )
    | ~ ( v13_waybel_0 @ sk_C_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ~ ( v13_waybel_0 @ sk_C_1 @ sk_B_2 )
    | ~ ( v12_waybel_0 @ sk_C_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['34'])).

thf('41',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_A_3 )
    | ~ ( v13_waybel_0 @ sk_D @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_A_3 )
   <= ( v12_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v12_waybel_0 @ B @ A )
          <=> ( r1_tarski @ ( k3_waybel_0 @ A @ B ) @ B ) ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v12_waybel_0 @ X17 @ X18 )
      | ( r1_tarski @ ( k3_waybel_0 @ X18 @ X17 ) @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t23_waybel_0])).

thf('45',plain,
    ( ~ ( l1_orders_2 @ sk_A_3 )
    | ( r1_tarski @ ( k3_waybel_0 @ sk_A_3 @ sk_C_1 ) @ sk_C_1 )
    | ~ ( v12_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_A_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_waybel_0 @ sk_A_3 @ sk_C_1 ) @ sk_C_1 )
    | ~ ( v12_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k3_waybel_0 @ sk_A_3 @ sk_C_1 ) @ sk_C_1 )
   <= ( v12_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ ( k3_waybel_0 @ X18 @ X17 ) @ X17 )
      | ( v12_waybel_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t23_waybel_0])).

thf('51',plain,
    ( ~ ( l1_orders_2 @ sk_B_2 )
    | ( v12_waybel_0 @ sk_C_1 @ sk_B_2 )
    | ~ ( r1_tarski @ ( k3_waybel_0 @ sk_B_2 @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_B_2 )
    | ~ ( r1_tarski @ ( k3_waybel_0 @ sk_B_2 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('55',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A_3 ) @ ( u1_orders_2 @ sk_A_3 ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_2 ) @ ( u1_orders_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k3_waybel_0 @ X15 @ X16 )
        = ( k3_waybel_0 @ X13 @ X14 ) )
      | ( X16 != X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X13 ) @ ( u1_orders_2 @ X13 ) ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t13_waybel_0])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X13 ) @ ( u1_orders_2 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k3_waybel_0 @ X15 @ X14 )
        = ( k3_waybel_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A_3 ) @ ( u1_orders_2 @ sk_A_3 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k3_waybel_0 @ sk_B_2 @ X1 )
        = ( k3_waybel_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ~ ( l1_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A_3 ) @ ( u1_orders_2 @ sk_A_3 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k3_waybel_0 @ sk_B_2 @ X1 )
        = ( k3_waybel_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( ( k3_waybel_0 @ sk_B_2 @ X0 )
        = ( k3_waybel_0 @ sk_A_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) )
      | ~ ( l1_orders_2 @ sk_A_3 ) ) ),
    inference(eq_res,[status(thm)],['60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( ( k3_waybel_0 @ sk_B_2 @ X0 )
        = ( k3_waybel_0 @ sk_A_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) )
    | ( ( k3_waybel_0 @ sk_B_2 @ sk_C_1 )
      = ( k3_waybel_0 @ sk_A_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k3_waybel_0 @ sk_B_2 @ sk_C_1 )
    = ( k3_waybel_0 @ sk_A_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_B_2 )
    | ~ ( r1_tarski @ ( k3_waybel_0 @ sk_A_3 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','66'])).

thf('68',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_B_2 )
   <= ( v12_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference('sup-',[status(thm)],['48','67'])).

thf('69',plain,
    ( ~ ( v12_waybel_0 @ sk_C_1 @ sk_B_2 )
   <= ~ ( v12_waybel_0 @ sk_C_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['34'])).

thf('70',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_B_2 )
    | ~ ( v12_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v13_waybel_0 @ sk_C_1 @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['39','40','70'])).

thf('72',plain,(
    ~ ( v13_waybel_0 @ sk_C_1 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['35','71'])).

thf('73',plain,(
    ~ ( r1_tarski @ ( k4_waybel_0 @ sk_A_3 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['30','72'])).

thf('74',plain,(
    ~ ( v13_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference('sup-',[status(thm)],['9','73'])).

thf('75',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B_2 )
    | ( v13_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference(split,[status(esa)],['2'])).

thf('76',plain,
    ( ( v12_waybel_0 @ sk_C_1 @ sk_B_2 )
   <= ( v12_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference('sup-',[status(thm)],['48','67'])).

thf('77',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B_2 )
    | ~ ( v13_waybel_0 @ sk_D @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B_2 )
   <= ~ ( v12_waybel_0 @ sk_D @ sk_B_2 ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v12_waybel_0 @ sk_C_1 @ sk_B_2 )
   <= ~ ( v12_waybel_0 @ sk_D @ sk_B_2 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v12_waybel_0 @ sk_D @ sk_B_2 )
    | ~ ( v12_waybel_0 @ sk_C_1 @ sk_A_3 ) ),
    inference('sup-',[status(thm)],['76','80'])).

thf('82',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','74','75','81'])).


%------------------------------------------------------------------------------
