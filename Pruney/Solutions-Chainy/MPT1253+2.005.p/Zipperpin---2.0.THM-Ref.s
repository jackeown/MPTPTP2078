%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YIXLdlZWj9

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:13 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 143 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  489 (1445 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( l1_pre_topc @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X48 @ X49 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k2_pre_topc @ X56 @ X55 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v4_pre_topc @ X50 @ X51 )
      | ~ ( r1_tarski @ X52 @ X50 )
      | ( r1_tarski @ ( k2_pre_topc @ X51 @ X52 ) @ X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['28','30'])).

thf('32',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['20','31','32'])).

thf('34',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','33'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YIXLdlZWj9
% 0.16/0.38  % Computer   : n010.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 09:26:15 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.39  % Running in FO mode
% 0.80/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.02  % Solved by: fo/fo7.sh
% 0.80/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.02  % done 865 iterations in 0.525s
% 0.80/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.02  % SZS output start Refutation
% 0.80/1.02  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.80/1.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.80/1.02  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.80/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.80/1.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/1.02  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.80/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.02  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.80/1.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.80/1.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.80/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.02  thf(t69_tops_1, conjecture,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( v4_pre_topc @ B @ A ) =>
% 0.80/1.02             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.80/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.02    (~( ![A:$i]:
% 0.80/1.02        ( ( l1_pre_topc @ A ) =>
% 0.80/1.02          ( ![B:$i]:
% 0.80/1.02            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02              ( ( v4_pre_topc @ B @ A ) =>
% 0.80/1.02                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.80/1.02    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.80/1.02  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('1', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(dt_k2_tops_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( ( l1_pre_topc @ A ) & 
% 0.80/1.02         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.80/1.02       ( m1_subset_1 @
% 0.80/1.02         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.80/1.02  thf('2', plain,
% 0.80/1.02      (![X48 : $i, X49 : $i]:
% 0.80/1.02         (~ (l1_pre_topc @ X48)
% 0.80/1.02          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.80/1.02          | (m1_subset_1 @ (k2_tops_1 @ X48 @ X49) @ 
% 0.80/1.02             (k1_zfmisc_1 @ (u1_struct_0 @ X48))))),
% 0.80/1.02      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.80/1.02  thf('3', plain,
% 0.80/1.02      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.80/1.02         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.02        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.02  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('5', plain,
% 0.80/1.02      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.80/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.02  thf('6', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(redefinition_k4_subset_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.80/1.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.80/1.02       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.80/1.02  thf('7', plain,
% 0.80/1.02      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.80/1.02          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 0.80/1.02          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 0.80/1.02      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.80/1.02  thf('8', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.80/1.02            = (k2_xboole_0 @ sk_B @ X0))
% 0.80/1.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.80/1.02      inference('sup-', [status(thm)], ['6', '7'])).
% 0.80/1.02  thf('9', plain,
% 0.80/1.02      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.80/1.02         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['5', '8'])).
% 0.80/1.02  thf('10', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(t65_tops_1, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( k2_pre_topc @ A @ B ) =
% 0.80/1.02             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.80/1.02  thf('11', plain,
% 0.80/1.02      (![X55 : $i, X56 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.80/1.02          | ((k2_pre_topc @ X56 @ X55)
% 0.80/1.02              = (k4_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 0.80/1.02                 (k2_tops_1 @ X56 @ X55)))
% 0.80/1.02          | ~ (l1_pre_topc @ X56))),
% 0.80/1.02      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.80/1.02  thf('12', plain,
% 0.80/1.02      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.02        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.80/1.02            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.80/1.02               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.80/1.02      inference('sup-', [status(thm)], ['10', '11'])).
% 0.80/1.02  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('14', plain,
% 0.80/1.02      (((k2_pre_topc @ sk_A @ sk_B)
% 0.80/1.02         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.80/1.02            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.02      inference('demod', [status(thm)], ['12', '13'])).
% 0.80/1.02  thf('15', plain,
% 0.80/1.02      (((k2_pre_topc @ sk_A @ sk_B)
% 0.80/1.02         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['9', '14'])).
% 0.80/1.02  thf('16', plain,
% 0.80/1.02      (((k2_pre_topc @ sk_A @ sk_B)
% 0.80/1.02         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['9', '14'])).
% 0.80/1.02  thf(t7_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.80/1.02  thf('17', plain,
% 0.80/1.02      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.80/1.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.80/1.02  thf(d10_xboole_0, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.80/1.02  thf('18', plain,
% 0.80/1.02      (![X10 : $i, X12 : $i]:
% 0.80/1.02         (((X10) = (X12))
% 0.80/1.02          | ~ (r1_tarski @ X12 @ X10)
% 0.80/1.02          | ~ (r1_tarski @ X10 @ X12))),
% 0.80/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.02  thf('19', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.80/1.02          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.02  thf('20', plain,
% 0.80/1.02      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.80/1.02        | ((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['16', '19'])).
% 0.80/1.02  thf('21', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('22', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(t31_tops_1, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ![C:$i]:
% 0.80/1.02             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.80/1.02                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.80/1.02  thf('23', plain,
% 0.80/1.02      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.80/1.02          | ~ (v4_pre_topc @ X50 @ X51)
% 0.80/1.02          | ~ (r1_tarski @ X52 @ X50)
% 0.80/1.02          | (r1_tarski @ (k2_pre_topc @ X51 @ X52) @ X50)
% 0.80/1.02          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.80/1.02          | ~ (l1_pre_topc @ X51))),
% 0.80/1.02      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.80/1.02  thf('24', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (l1_pre_topc @ sk_A)
% 0.80/1.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.02          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 0.80/1.02          | ~ (r1_tarski @ X0 @ sk_B)
% 0.80/1.02          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['22', '23'])).
% 0.80/1.02  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('26', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('27', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.02          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 0.80/1.02          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.80/1.02      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.80/1.02  thf('28', plain,
% 0.80/1.02      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.80/1.02        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.80/1.02      inference('sup-', [status(thm)], ['21', '27'])).
% 0.80/1.02  thf('29', plain,
% 0.80/1.02      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.80/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.02  thf('30', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.80/1.02      inference('simplify', [status(thm)], ['29'])).
% 0.80/1.02  thf('31', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 0.80/1.02      inference('demod', [status(thm)], ['28', '30'])).
% 0.80/1.02  thf('32', plain,
% 0.80/1.02      (((k2_pre_topc @ sk_A @ sk_B)
% 0.80/1.02         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['9', '14'])).
% 0.80/1.02  thf('33', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.80/1.02      inference('demod', [status(thm)], ['20', '31', '32'])).
% 0.80/1.02  thf('34', plain,
% 0.80/1.02      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.02      inference('demod', [status(thm)], ['15', '33'])).
% 0.80/1.02  thf(commutativity_k2_tarski, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.80/1.02  thf('35', plain,
% 0.80/1.02      (![X19 : $i, X20 : $i]:
% 0.80/1.02         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.80/1.02  thf(l51_zfmisc_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.80/1.02  thf('36', plain,
% 0.80/1.02      (![X21 : $i, X22 : $i]:
% 0.80/1.02         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.80/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.80/1.02  thf('37', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['35', '36'])).
% 0.80/1.02  thf('38', plain,
% 0.80/1.02      (![X21 : $i, X22 : $i]:
% 0.80/1.02         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.80/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.80/1.02  thf('39', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['37', '38'])).
% 0.80/1.02  thf('40', plain,
% 0.80/1.02      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.80/1.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.80/1.02  thf('41', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['39', '40'])).
% 0.80/1.02  thf('42', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.80/1.02      inference('sup+', [status(thm)], ['34', '41'])).
% 0.80/1.02  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.80/1.02  
% 0.80/1.02  % SZS output end Refutation
% 0.80/1.02  
% 0.80/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
