%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bFcaXboiZr

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 140 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  585 (2242 expanded)
%              Number of equality atoms :   36 ( 141 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t55_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( v3_pre_topc @ D @ B )
                       => ( ( k1_tops_1 @ B @ D )
                          = D ) )
                      & ( ( ( k1_tops_1 @ A @ C )
                          = C )
                       => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_tops_1])).

thf('0',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
    | ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) @ X11 )
      | ( v4_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('14',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k1_tops_1 @ X7 @ X6 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_pre_topc @ X7 @ ( k3_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_tops_1 @ sk_B @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['4','27'])).

thf('29',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
   <= ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
    | ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X8 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('37',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('43',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
     != sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k1_tops_1 @ sk_B @ sk_D )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['31','33','43'])).

thf('45',plain,(
    ( k1_tops_1 @ sk_B @ sk_D )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['30','44'])).

thf('46',plain,(
    ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['28','45'])).

thf('47',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('48',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bFcaXboiZr
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:39 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 69 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.49  thf(t55_tops_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_pre_topc @ B ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.21/0.49                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.21/0.49                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.21/0.49                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( l1_pre_topc @ B ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49                      ( ( ( v3_pre_topc @ D @ B ) =>
% 0.21/0.49                          ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.21/0.49                        ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.21/0.49                          ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t55_tops_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_D @ sk_B) | ((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) | ((v3_pre_topc @ sk_D @ sk_B))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49         (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_D @ sk_B) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k3_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf(t29_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.49             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.49          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10) @ X11)
% 0.21/0.49          | (v4_pre_topc @ X10 @ X11)
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B)
% 0.21/0.49        | ~ (v3_pre_topc @ 
% 0.21/0.49             (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49              (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)) @ 
% 0.21/0.49             sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49         (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B)
% 0.21/0.49        | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))
% 0.21/0.49         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf(t52_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.49             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.49               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.49          | ~ (v4_pre_topc @ X4 @ X5)
% 0.21/0.49          | ((k2_pre_topc @ X5 @ X4) = (X4))
% 0.21/0.49          | ~ (l1_pre_topc @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | ((k2_pre_topc @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.49            = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((((k2_pre_topc @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.49          = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.49        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((((k2_pre_topc @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.21/0.49          = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.21/0.49         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d1_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.49             ( k3_subset_1 @
% 0.21/0.49               ( u1_struct_0 @ A ) @ 
% 0.21/0.49               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.49          | ((k1_tops_1 @ X7 @ X6)
% 0.21/0.49              = (k3_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.49                 (k2_pre_topc @ X7 @ (k3_subset_1 @ (u1_struct_0 @ X7) @ X6))))
% 0.21/0.49          | ~ (l1_pre_topc @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | ((k1_tops_1 @ sk_B @ sk_D)
% 0.21/0.49            = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49               (k2_pre_topc @ sk_B @ 
% 0.21/0.49                (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((k1_tops_1 @ sk_B @ sk_D)
% 0.21/0.49         = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49            (k2_pre_topc @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))))),
% 0.21/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((((k1_tops_1 @ sk_B @ sk_D)
% 0.21/0.49          = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49             (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))))
% 0.21/0.49         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.21/0.49         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['4', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D)) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D)))
% 0.21/0.49         <= (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))) | 
% 0.21/0.49       ~ ((v3_pre_topc @ sk_C @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['29'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D))
% 0.21/0.49        | ((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) | 
% 0.21/0.49       ~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.21/0.49         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['32'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(fc9_tops_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X8)
% 0.21/0.49          | ~ (v2_pre_topc @ X8)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.49          | (v3_pre_topc @ (k1_tops_1 @ X8 @ X9) @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_C @ sk_A))
% 0.21/0.49         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['34', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['29'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (((v3_pre_topc @ sk_C @ sk_A)) | ~ (((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain, (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['31', '33', '43'])).
% 0.21/0.49  thf('45', plain, (((k1_tops_1 @ sk_B @ sk_D) != (sk_D))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['30', '44'])).
% 0.21/0.49  thf('46', plain, (~ ((v3_pre_topc @ sk_D @ sk_B))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['28', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (~ ((v3_pre_topc @ sk_C @ sk_A)) | ((v3_pre_topc @ sk_D @ sk_B))),
% 0.21/0.49      inference('split', [status(esa)], ['5'])).
% 0.21/0.49  thf('48', plain, ($false),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['1', '46', '47', '43'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
