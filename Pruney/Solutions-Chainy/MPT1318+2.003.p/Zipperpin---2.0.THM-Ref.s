%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hP4POfF3Vz

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:37 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   68 (  84 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  476 ( 793 expanded)
%              Number of equality atoms :   33 (  36 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t38_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_tops_2])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X33 @ X32 ) )
        = X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X3 @ X4 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X14 @ X19 )
      | ( X19
       != ( k2_enumset1 @ X18 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X14 @ ( k2_enumset1 @ X18 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X12 @ X8 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('29',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['10','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hP4POfF3Vz
% 0.14/0.37  % Computer   : n004.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:03:54 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 58 iterations in 0.035s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.52  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.24/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.24/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.24/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.24/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.24/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.24/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.52  thf(t38_tops_2, conjecture,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( l1_pre_topc @ A ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52           ( ![C:$i]:
% 0.24/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52               ( m1_subset_1 @
% 0.24/0.52                 ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.24/0.52                 ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i]:
% 0.24/0.52        ( ( l1_pre_topc @ A ) =>
% 0.24/0.52          ( ![B:$i]:
% 0.24/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52              ( ![C:$i]:
% 0.24/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52                  ( m1_subset_1 @
% 0.24/0.52                    ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.24/0.52                    ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t38_tops_2])).
% 0.24/0.52  thf('0', plain,
% 0.24/0.52      (~ (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.24/0.52          (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C))))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t29_pre_topc, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( l1_pre_topc @ A ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.24/0.52  thf('2', plain,
% 0.24/0.52      (![X32 : $i, X33 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.24/0.52          | ((u1_struct_0 @ (k1_pre_topc @ X33 @ X32)) = (X32))
% 0.24/0.52          | ~ (l1_pre_topc @ X33))),
% 0.24/0.52      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.24/0.52  thf('3', plain,
% 0.24/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.52  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('5', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.24/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.24/0.52  thf('6', plain,
% 0.24/0.52      (~ (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.24/0.52          (k1_zfmisc_1 @ sk_C))),
% 0.24/0.52      inference('demod', [status(thm)], ['0', '5'])).
% 0.24/0.52  thf('7', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(redefinition_k9_subset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.24/0.52  thf('8', plain,
% 0.24/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.24/0.52         (((k9_subset_1 @ X24 @ X22 @ X23) = (k3_xboole_0 @ X22 @ X23))
% 0.24/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.24/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.24/0.52           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.24/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.52  thf('10', plain,
% 0.24/0.52      (~ (m1_subset_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_C))),
% 0.24/0.52      inference('demod', [status(thm)], ['6', '9'])).
% 0.24/0.52  thf('11', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(commutativity_k9_subset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.24/0.52  thf('12', plain,
% 0.24/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.52         (((k9_subset_1 @ X5 @ X7 @ X6) = (k9_subset_1 @ X5 @ X6 @ X7))
% 0.24/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.24/0.52      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.24/0.52  thf('13', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.24/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.52  thf('14', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('15', plain,
% 0.24/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.24/0.52         (((k9_subset_1 @ X24 @ X22 @ X23) = (k3_xboole_0 @ X22 @ X23))
% 0.24/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.24/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.24/0.52  thf('16', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.24/0.52           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.24/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.24/0.52  thf('17', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((k3_xboole_0 @ X0 @ sk_B)
% 0.24/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.24/0.52      inference('demod', [status(thm)], ['13', '16'])).
% 0.24/0.52  thf('18', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.24/0.52           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.24/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.24/0.52  thf(t70_enumset1, axiom,
% 0.24/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.24/0.52  thf('20', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]:
% 0.24/0.52         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.24/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.24/0.52  thf(t71_enumset1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.24/0.52  thf('21', plain,
% 0.24/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.24/0.52         ((k2_enumset1 @ X2 @ X2 @ X3 @ X4) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 0.24/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.24/0.52  thf(d2_enumset1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.24/0.52     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.24/0.52       ( ![F:$i]:
% 0.24/0.52         ( ( r2_hidden @ F @ E ) <=>
% 0.24/0.52           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.24/0.52                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.24/0.52  thf(zf_stmt_2, axiom,
% 0.24/0.52    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.24/0.52     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.24/0.52       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.24/0.52         ( ( F ) != ( D ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_3, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.24/0.52     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.24/0.52       ( ![F:$i]:
% 0.24/0.52         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.24/0.52  thf('22', plain,
% 0.24/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.52         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.24/0.52          | (r2_hidden @ X14 @ X19)
% 0.24/0.52          | ((X19) != (k2_enumset1 @ X18 @ X17 @ X16 @ X15)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.24/0.52  thf('23', plain,
% 0.24/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.24/0.52         ((r2_hidden @ X14 @ (k2_enumset1 @ X18 @ X17 @ X16 @ X15))
% 0.24/0.52          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.24/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.52         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.24/0.52          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.24/0.52      inference('sup+', [status(thm)], ['21', '23'])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.24/0.52         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X8))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.24/0.52  thf('26', plain,
% 0.24/0.52      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.24/0.52         ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X12 @ X8)),
% 0.24/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.24/0.52  thf('27', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.52         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.24/0.52      inference('sup-', [status(thm)], ['24', '26'])).
% 0.24/0.52  thf('28', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.24/0.52      inference('sup+', [status(thm)], ['20', '27'])).
% 0.24/0.52  thf(t4_setfam_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.24/0.52  thf('29', plain,
% 0.24/0.52      (![X30 : $i, X31 : $i]:
% 0.24/0.52         ((r1_tarski @ (k1_setfam_1 @ X30) @ X31) | ~ (r2_hidden @ X31 @ X30))),
% 0.24/0.52      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.24/0.52  thf('30', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]:
% 0.24/0.52         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 0.24/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.24/0.52  thf(t12_setfam_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.24/0.52  thf('31', plain,
% 0.24/0.52      (![X25 : $i, X26 : $i]:
% 0.24/0.52         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 0.24/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.24/0.52  thf('32', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.24/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.24/0.52  thf(t3_subset, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.52  thf('33', plain,
% 0.24/0.52      (![X27 : $i, X29 : $i]:
% 0.24/0.52         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 0.24/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.52  thf('34', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]:
% 0.24/0.52         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.24/0.52  thf('35', plain,
% 0.24/0.52      ((m1_subset_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_C))),
% 0.24/0.52      inference('sup+', [status(thm)], ['19', '34'])).
% 0.24/0.52  thf('36', plain, ($false), inference('demod', [status(thm)], ['10', '35'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
