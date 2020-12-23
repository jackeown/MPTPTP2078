%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VwVfONm25w

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:24 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 221 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  606 (3751 expanded)
%              Number of equality atoms :   31 ( 252 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(t20_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( C = D )
                      & ( v2_tops_2 @ C @ A ) )
                   => ( v2_tops_2 @ D @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                   => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                        & ( C = D )
                        & ( v2_tops_2 @ C @ A ) )
                     => ( v2_tops_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_waybel_9])).

thf('0',plain,(
    ~ ( v2_tops_2 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v2_tops_2 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('13',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('20',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['21'])).

thf(t16_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X8 ) @ X7 ) @ X8 )
      | ( v2_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tops_2 @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_tops_2 @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_B )
    | ( v2_tops_2 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('31',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['21'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( r1_tarski @ X9 @ ( u1_pre_topc @ X10 ) )
      | ( v1_tops_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v1_tops_2 @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_tops_2 @ X9 @ X10 )
      | ( r1_tarski @ X9 @ ( u1_pre_topc @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v2_tops_2 @ X7 @ X8 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X8 ) @ X7 ) @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_tops_2 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','48'])).

thf('50',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,(
    v2_tops_2 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['28','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['2','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VwVfONm25w
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 139 iterations in 0.130s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.37/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.58  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.37/0.58  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.37/0.58  thf(t20_waybel_9, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( l1_pre_topc @ B ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( m1_subset_1 @
% 0.37/0.58                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58               ( ![D:$i]:
% 0.37/0.58                 ( ( m1_subset_1 @
% 0.37/0.58                     D @ 
% 0.37/0.58                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.37/0.58                   ( ( ( ( g1_pre_topc @
% 0.37/0.58                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.58                         ( g1_pre_topc @
% 0.37/0.58                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.37/0.58                       ( ( C ) = ( D ) ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.37/0.58                     ( v2_tops_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( l1_pre_topc @ A ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( l1_pre_topc @ B ) =>
% 0.37/0.58              ( ![C:$i]:
% 0.37/0.58                ( ( m1_subset_1 @
% 0.37/0.58                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58                  ( ![D:$i]:
% 0.37/0.58                    ( ( m1_subset_1 @
% 0.37/0.58                        D @ 
% 0.37/0.58                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.37/0.58                      ( ( ( ( g1_pre_topc @
% 0.37/0.58                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.58                            ( g1_pre_topc @
% 0.37/0.58                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.37/0.58                          ( ( C ) = ( D ) ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.37/0.58                        ( v2_tops_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t20_waybel_9])).
% 0.37/0.58  thf('0', plain, (~ (v2_tops_2 @ sk_D @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('1', plain, (((sk_C) = (sk_D))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('2', plain, (~ (v2_tops_2 @ sk_C @ sk_B)),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ 
% 0.37/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(dt_u1_pre_topc, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( m1_subset_1 @
% 0.37/0.58         ( u1_pre_topc @ A ) @ 
% 0.37/0.58         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X2 : $i]:
% 0.37/0.58         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.37/0.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.37/0.58          | ~ (l1_pre_topc @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.37/0.58  thf(free_g1_pre_topc, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.58       ( ![C:$i,D:$i]:
% 0.37/0.58         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.37/0.58           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.58         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.37/0.58          | ((X6) = (X4))
% 0.37/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.37/0.58      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ X0)
% 0.37/0.58          | ((u1_pre_topc @ X0) = (X1))
% 0.37/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.37/0.58              != (g1_pre_topc @ X2 @ X1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.58            != (g1_pre_topc @ X1 @ X0))
% 0.37/0.58          | ((u1_pre_topc @ sk_B) = (X0))
% 0.37/0.58          | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.58  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.58            != (g1_pre_topc @ X1 @ X0))
% 0.37/0.58          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.37/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('11', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.37/0.58      inference('eq_res', [status(thm)], ['10'])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X2 : $i]:
% 0.37/0.58         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.37/0.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.37/0.58          | ~ (l1_pre_topc @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.58         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.37/0.58        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.58         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.37/0.58          | ((X5) = (X3))
% 0.37/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.37/0.58      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((u1_struct_0 @ sk_B) = (X0))
% 0.37/0.58          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.58              != (g1_pre_topc @ X0 @ X1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('19', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.37/0.58      inference('eq_res', [status(thm)], ['10'])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((u1_struct_0 @ sk_B) = (X0))
% 0.37/0.58          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.58              != (g1_pre_topc @ X0 @ X1)))),
% 0.37/0.58      inference('demod', [status(thm)], ['17', '20'])).
% 0.37/0.58  thf('22', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('eq_res', [status(thm)], ['21'])).
% 0.37/0.58  thf(t16_tops_2, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @
% 0.37/0.58             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58           ( ( v2_tops_2 @ B @ A ) <=>
% 0.37/0.58             ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (![X7 : $i, X8 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X7 @ 
% 0.37/0.58             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.37/0.58          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X8) @ X7) @ X8)
% 0.37/0.58          | (v2_tops_2 @ X7 @ X8)
% 0.37/0.58          | ~ (l1_pre_topc @ X8))),
% 0.37/0.58      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X0 @ 
% 0.37/0.58             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.58          | (v2_tops_2 @ X0 @ sk_B)
% 0.37/0.58          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ X0) @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.59  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('26', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.37/0.59      inference('eq_res', [status(thm)], ['21'])).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.37/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.59          | (v2_tops_2 @ X0 @ sk_B)
% 0.37/0.59          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      ((~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_B)
% 0.37/0.59        | (v2_tops_2 @ sk_C @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['3', '27'])).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(dt_k7_setfam_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.59       ( m1_subset_1 @
% 0.37/0.59         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((m1_subset_1 @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.37/0.59           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.37/0.59      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.37/0.59  thf('31', plain,
% 0.37/0.59      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.59  thf('32', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.37/0.59      inference('eq_res', [status(thm)], ['21'])).
% 0.37/0.59  thf(t78_tops_2, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( l1_pre_topc @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( m1_subset_1 @
% 0.37/0.59             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.59           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.37/0.59  thf('33', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X9 @ 
% 0.37/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.37/0.59          | ~ (r1_tarski @ X9 @ (u1_pre_topc @ X10))
% 0.37/0.59          | (v1_tops_2 @ X9 @ X10)
% 0.37/0.59          | ~ (l1_pre_topc @ X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.37/0.59  thf('34', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.37/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.59          | (v1_tops_2 @ X0 @ sk_B)
% 0.37/0.59          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.59  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('36', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.37/0.59      inference('eq_res', [status(thm)], ['10'])).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.37/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.59          | (v1_tops_2 @ X0 @ sk_B)
% 0.37/0.59          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      ((~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.59           (u1_pre_topc @ sk_A))
% 0.37/0.59        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['31', '37'])).
% 0.37/0.59  thf('39', plain,
% 0.37/0.59      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X9 @ 
% 0.37/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.37/0.59          | ~ (v1_tops_2 @ X9 @ X10)
% 0.37/0.59          | (r1_tarski @ X9 @ (u1_pre_topc @ X10))
% 0.37/0.59          | ~ (l1_pre_topc @ X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.37/0.59  thf('41', plain,
% 0.37/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.59        | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.59           (u1_pre_topc @ sk_A))
% 0.37/0.59        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.59  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('43', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('44', plain,
% 0.37/0.59      (![X7 : $i, X8 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X7 @ 
% 0.37/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.37/0.59          | ~ (v2_tops_2 @ X7 @ X8)
% 0.37/0.59          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X8) @ X7) @ X8)
% 0.37/0.59          | ~ (l1_pre_topc @ X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.37/0.59  thf('45', plain,
% 0.37/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.59        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.37/0.59        | ~ (v2_tops_2 @ sk_C @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.59  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('47', plain, ((v2_tops_2 @ sk_C @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('48', plain,
% 0.37/0.59      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)),
% 0.37/0.59      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.37/0.59  thf('49', plain,
% 0.37/0.59      ((r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.59        (u1_pre_topc @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['41', '42', '48'])).
% 0.37/0.59  thf('50', plain,
% 0.37/0.59      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_B)),
% 0.37/0.59      inference('demod', [status(thm)], ['38', '49'])).
% 0.37/0.59  thf('51', plain, ((v2_tops_2 @ sk_C @ sk_B)),
% 0.37/0.59      inference('demod', [status(thm)], ['28', '50'])).
% 0.37/0.59  thf('52', plain, ($false), inference('demod', [status(thm)], ['2', '51'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
