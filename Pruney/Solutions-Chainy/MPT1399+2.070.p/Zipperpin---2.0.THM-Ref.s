%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SyThjcGN08

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 (  98 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :  417 (1164 expanded)
%              Number of equality atoms :    8 (  29 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('7',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X12: $i] :
      ( ~ ( v3_pre_topc @ X12 @ sk_A )
      | ~ ( v4_pre_topc @ X12 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X12 )
      | ( r2_hidden @ X12 @ sk_C )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X12: $i] :
      ( ~ ( v3_pre_topc @ X12 @ sk_A )
      | ~ ( v4_pre_topc @ X12 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X12 )
      | ( r2_hidden @ X12 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('26',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','30'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('39',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SyThjcGN08
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:50:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 58 iterations in 0.029s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.45  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.45  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.45  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.45  thf(t28_connsp_2, conjecture,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.45           ( ![C:$i]:
% 0.19/0.45             ( ( m1_subset_1 @
% 0.19/0.45                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.45               ( ~( ( ![D:$i]:
% 0.19/0.45                      ( ( m1_subset_1 @
% 0.19/0.45                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.45                        ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.45                          ( ( v3_pre_topc @ D @ A ) & 
% 0.19/0.45                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.19/0.45                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i]:
% 0.19/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.45            ( l1_pre_topc @ A ) ) =>
% 0.19/0.45          ( ![B:$i]:
% 0.19/0.45            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.45              ( ![C:$i]:
% 0.19/0.45                ( ( m1_subset_1 @
% 0.19/0.45                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.45                  ( ~( ( ![D:$i]:
% 0.19/0.45                         ( ( m1_subset_1 @
% 0.19/0.45                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.45                           ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.45                             ( ( v3_pre_topc @ D @ A ) & 
% 0.19/0.45                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.19/0.45                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.19/0.45  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t2_subset, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.45       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X3 : $i, X4 : $i]:
% 0.19/0.45         ((r2_hidden @ X3 @ X4)
% 0.19/0.45          | (v1_xboole_0 @ X4)
% 0.19/0.45          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.19/0.45      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.45  thf(fc10_tops_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.45       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (![X11 : $i]:
% 0.19/0.45         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.19/0.45          | ~ (l1_pre_topc @ X11)
% 0.19/0.45          | ~ (v2_pre_topc @ X11))),
% 0.19/0.45      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.19/0.45  thf(d3_struct_0, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X7 : $i]:
% 0.19/0.45         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.19/0.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.45  thf(fc4_pre_topc, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.45       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X10 : $i]:
% 0.19/0.45         ((v4_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.19/0.45          | ~ (l1_pre_topc @ X10)
% 0.19/0.45          | ~ (v2_pre_topc @ X10))),
% 0.19/0.45      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      (![X7 : $i]:
% 0.19/0.45         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.19/0.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.45  thf(dt_k2_subset_1, axiom,
% 0.19/0.45    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.45  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.45  thf('9', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.19/0.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.45  thf('10', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.19/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (![X12 : $i]:
% 0.19/0.45         (~ (v3_pre_topc @ X12 @ sk_A)
% 0.19/0.45          | ~ (v4_pre_topc @ X12 @ sk_A)
% 0.19/0.45          | ~ (r2_hidden @ sk_B @ X12)
% 0.19/0.45          | (r2_hidden @ X12 @ sk_C)
% 0.19/0.45          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('12', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (![X12 : $i]:
% 0.19/0.45         (~ (v3_pre_topc @ X12 @ sk_A)
% 0.19/0.45          | ~ (v4_pre_topc @ X12 @ sk_A)
% 0.19/0.45          | ~ (r2_hidden @ sk_B @ X12)
% 0.19/0.45          | (r2_hidden @ X12 @ k1_xboole_0)
% 0.19/0.45          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.45      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.45  thf('14', plain,
% 0.19/0.45      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.19/0.45        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.45        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['10', '13'])).
% 0.19/0.45  thf('15', plain,
% 0.19/0.45      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.45        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.45        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.45        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['7', '14'])).
% 0.19/0.45  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(dt_l1_pre_topc, axiom,
% 0.19/0.45    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.45  thf('17', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.45  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.45      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.45  thf('19', plain,
% 0.19/0.45      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.45        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.19/0.45        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.19/0.45      inference('demod', [status(thm)], ['15', '18'])).
% 0.19/0.45  thf('20', plain,
% 0.19/0.45      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.45        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.45        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.19/0.45        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['6', '19'])).
% 0.19/0.45  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('23', plain,
% 0.19/0.45      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.19/0.45        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.19/0.45      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.45  thf('24', plain,
% 0.19/0.45      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.45        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.45        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['5', '23'])).
% 0.19/0.45  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.45      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.45  thf('26', plain,
% 0.19/0.45      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.19/0.45        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.19/0.45      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.45  thf('27', plain,
% 0.19/0.45      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.45        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.45        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.19/0.45        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '26'])).
% 0.19/0.45  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('30', plain,
% 0.19/0.45      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.19/0.45        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.45      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.19/0.45  thf('31', plain,
% 0.19/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['3', '30'])).
% 0.19/0.45  thf(t7_ordinal1, axiom,
% 0.19/0.45    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.45  thf('32', plain,
% 0.19/0.45      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 0.19/0.45      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.45  thf('33', plain,
% 0.19/0.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.45        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.45  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.45  thf('35', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.45      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.45  thf(fc2_struct_0, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.45       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.45  thf('36', plain,
% 0.19/0.45      (![X9 : $i]:
% 0.19/0.45         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.19/0.45          | ~ (l1_struct_0 @ X9)
% 0.19/0.45          | (v2_struct_0 @ X9))),
% 0.19/0.45      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.45  thf('37', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.45  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.45      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.45  thf('39', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.45      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.45  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
