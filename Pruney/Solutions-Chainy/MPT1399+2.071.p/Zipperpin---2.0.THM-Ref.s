%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RMeOSQgivK

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:12 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 112 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :   18
%              Number of atoms          :  422 (1330 expanded)
%              Number of equality atoms :   17 (  43 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X14: $i] :
      ( ~ ( v3_pre_topc @ X14 @ sk_A )
      | ~ ( v4_pre_topc @ X14 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X14 )
      | ( r2_hidden @ X14 @ sk_C )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','29'])).

thf('31',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('33',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('41',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('42',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('45',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RMeOSQgivK
% 0.17/0.38  % Computer   : n024.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 10:13:06 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 52 iterations in 0.026s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.24/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.24/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.24/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.52  thf(t28_connsp_2, conjecture,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52           ( ![C:$i]:
% 0.24/0.52             ( ( m1_subset_1 @
% 0.24/0.52                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.52               ( ~( ( ![D:$i]:
% 0.24/0.52                      ( ( m1_subset_1 @
% 0.24/0.52                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52                        ( ( r2_hidden @ D @ C ) <=>
% 0.24/0.52                          ( ( v3_pre_topc @ D @ A ) & 
% 0.24/0.52                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.24/0.52                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i]:
% 0.24/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.52            ( l1_pre_topc @ A ) ) =>
% 0.24/0.52          ( ![B:$i]:
% 0.24/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52              ( ![C:$i]:
% 0.24/0.52                ( ( m1_subset_1 @
% 0.24/0.52                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.52                  ( ~( ( ![D:$i]:
% 0.24/0.52                         ( ( m1_subset_1 @
% 0.24/0.52                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52                           ( ( r2_hidden @ D @ C ) <=>
% 0.24/0.52                             ( ( v3_pre_topc @ D @ A ) & 
% 0.24/0.52                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.24/0.52                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.24/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(d3_struct_0, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      (![X9 : $i]:
% 0.24/0.52         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.24/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.52  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t2_subset, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.24/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.24/0.52  thf('3', plain,
% 0.24/0.52      (![X7 : $i, X8 : $i]:
% 0.24/0.52         ((r2_hidden @ X7 @ X8)
% 0.24/0.52          | (v1_xboole_0 @ X8)
% 0.24/0.52          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.24/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.24/0.52  thf('4', plain,
% 0.24/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.52  thf(fc10_tops_1, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.24/0.52  thf('5', plain,
% 0.24/0.52      (![X13 : $i]:
% 0.24/0.52         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 0.24/0.52          | ~ (l1_pre_topc @ X13)
% 0.24/0.52          | ~ (v2_pre_topc @ X13))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.24/0.52  thf('6', plain,
% 0.24/0.52      (![X9 : $i]:
% 0.24/0.52         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.24/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.52  thf(fc4_pre_topc, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.24/0.52  thf('7', plain,
% 0.24/0.52      (![X11 : $i]:
% 0.24/0.52         ((v4_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.24/0.52          | ~ (l1_pre_topc @ X11)
% 0.24/0.52          | ~ (v2_pre_topc @ X11))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.24/0.52  thf('8', plain,
% 0.24/0.52      (![X9 : $i]:
% 0.24/0.52         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.24/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.52  thf(dt_k2_subset_1, axiom,
% 0.24/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.24/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.24/0.52  thf('10', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.24/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.24/0.52  thf('11', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.24/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.52  thf('12', plain,
% 0.24/0.52      (![X14 : $i]:
% 0.24/0.52         (~ (v3_pre_topc @ X14 @ sk_A)
% 0.24/0.52          | ~ (v4_pre_topc @ X14 @ sk_A)
% 0.24/0.52          | ~ (r2_hidden @ sk_B @ X14)
% 0.24/0.52          | (r2_hidden @ X14 @ sk_C)
% 0.24/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('13', plain,
% 0.24/0.52      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.24/0.52        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.24/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.52  thf('14', plain,
% 0.24/0.52      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.24/0.52        | ~ (l1_struct_0 @ sk_A)
% 0.24/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.24/0.52        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.24/0.52      inference('sup-', [status(thm)], ['8', '13'])).
% 0.24/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(dt_l1_pre_topc, axiom,
% 0.24/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.52  thf('16', plain,
% 0.24/0.52      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.52  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.52  thf('18', plain,
% 0.24/0.52      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.24/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.24/0.52        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.24/0.52      inference('demod', [status(thm)], ['14', '17'])).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.24/0.52        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['7', '18'])).
% 0.24/0.52  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('22', plain,
% 0.24/0.52      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.24/0.52        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.24/0.52  thf(t113_zfmisc_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.52  thf('23', plain,
% 0.24/0.52      (![X1 : $i, X2 : $i]:
% 0.24/0.52         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.24/0.52  thf('25', plain, (((sk_C) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('26', plain, (((sk_C) = (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('27', plain, (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ sk_C) = (sk_C))),
% 0.24/0.52      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.24/0.52  thf(t152_zfmisc_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.24/0.52  thf('28', plain,
% 0.24/0.52      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.24/0.52      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.24/0.52  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.24/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.24/0.52  thf('30', plain,
% 0.24/0.52      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.24/0.52        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('clc', [status(thm)], ['22', '29'])).
% 0.24/0.52  thf('31', plain,
% 0.24/0.52      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.24/0.52        | ~ (l1_struct_0 @ sk_A)
% 0.24/0.52        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['6', '30'])).
% 0.24/0.52  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.52  thf('33', plain,
% 0.24/0.52      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.24/0.52        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('demod', [status(thm)], ['31', '32'])).
% 0.24/0.52  thf('34', plain,
% 0.24/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['5', '33'])).
% 0.24/0.52  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('37', plain, (~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.24/0.52  thf('38', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['4', '37'])).
% 0.24/0.52  thf('39', plain,
% 0.24/0.52      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.24/0.52      inference('sup+', [status(thm)], ['1', '38'])).
% 0.24/0.52  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.52  thf('41', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.24/0.52  thf(fc5_struct_0, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.24/0.52       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.24/0.52  thf('42', plain,
% 0.24/0.52      (![X12 : $i]:
% 0.24/0.52         (~ (v1_xboole_0 @ (k2_struct_0 @ X12))
% 0.24/0.52          | ~ (l1_struct_0 @ X12)
% 0.24/0.52          | (v2_struct_0 @ X12))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.24/0.52  thf('43', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.24/0.52  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.52  thf('45', plain, ((v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.52  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
