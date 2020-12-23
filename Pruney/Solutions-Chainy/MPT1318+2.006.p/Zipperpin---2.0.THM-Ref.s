%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RJQV41afpc

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:37 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 128 expanded)
%              Number of leaves         :   38 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  704 (1383 expanded)
%              Number of equality atoms :   49 (  66 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

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
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X61 @ X60 ) )
        = X60 )
      | ~ ( l1_pre_topc @ X61 ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k9_subset_1 @ X52 @ X50 @ X51 )
        = ( k3_xboole_0 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k9_subset_1 @ X27 @ X29 @ X28 )
        = ( k9_subset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k9_subset_1 @ X52 @ X50 @ X51 )
        = ( k3_xboole_0 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X3 @ X4 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X5 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k6_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t81_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k6_enumset1 @ X21 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t81_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(d5_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( ( I != G )
              & ( I != F )
              & ( I != E )
              & ( I != D )
              & ( I != C )
              & ( I != B )
              & ( I != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [I: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( I != A )
        & ( I != B )
        & ( I != C )
        & ( I != D )
        & ( I != E )
        & ( I != F )
        & ( I != G ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      | ( r2_hidden @ X39 @ X47 )
      | ( X47
       != ( k5_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ X39 @ ( k5_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 ) )
      | ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( X31 != X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X30: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ~ ( zip_tseitin_0 @ X30 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X30 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X0 @ ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','37'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('39',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X58 ) @ X59 )
      | ~ ( r2_hidden @ X59 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X53 @ X54 ) )
      = ( k3_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_C ),
    inference('sup+',[status(thm)],['21','42'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X55: $i,X57: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r1_tarski @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    m1_subset_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['20','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RJQV41afpc
% 0.11/0.30  % Computer   : n006.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 20:51:52 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  % Running portfolio for 600 s
% 0.11/0.30  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.31  % Number of cores: 8
% 0.11/0.31  % Python version: Python 3.6.8
% 0.11/0.31  % Running in FO mode
% 0.17/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.17/0.49  % Solved by: fo/fo7.sh
% 0.17/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.49  % done 85 iterations in 0.073s
% 0.17/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.17/0.49  % SZS output start Refutation
% 0.17/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.49  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.17/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.17/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.17/0.49  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.17/0.49                                           $i > $i).
% 0.17/0.49  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.17/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.17/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.17/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.17/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.17/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.17/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.17/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.17/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.17/0.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.17/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.17/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.17/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.17/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.17/0.49                                               $i > $i > $o).
% 0.17/0.49  thf(t38_tops_2, conjecture,
% 0.17/0.49    (![A:$i]:
% 0.17/0.49     ( ( l1_pre_topc @ A ) =>
% 0.17/0.49       ( ![B:$i]:
% 0.17/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.49           ( ![C:$i]:
% 0.17/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.49               ( m1_subset_1 @
% 0.17/0.49                 ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.17/0.49                 ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.17/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.49    (~( ![A:$i]:
% 0.17/0.49        ( ( l1_pre_topc @ A ) =>
% 0.17/0.49          ( ![B:$i]:
% 0.17/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.49              ( ![C:$i]:
% 0.17/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.49                  ( m1_subset_1 @
% 0.17/0.49                    ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.17/0.49                    ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.17/0.49    inference('cnf.neg', [status(esa)], [t38_tops_2])).
% 0.17/0.49  thf('0', plain,
% 0.17/0.49      (~ (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.17/0.49          (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C))))),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf('1', plain,
% 0.17/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf(t29_pre_topc, axiom,
% 0.17/0.49    (![A:$i]:
% 0.17/0.49     ( ( l1_pre_topc @ A ) =>
% 0.17/0.49       ( ![B:$i]:
% 0.17/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.49           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.17/0.49  thf('2', plain,
% 0.17/0.49      (![X60 : $i, X61 : $i]:
% 0.17/0.49         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 0.17/0.49          | ((u1_struct_0 @ (k1_pre_topc @ X61 @ X60)) = (X60))
% 0.17/0.49          | ~ (l1_pre_topc @ X61))),
% 0.17/0.49      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.17/0.49  thf('3', plain,
% 0.17/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.17/0.49        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C)))),
% 0.17/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.49  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf('5', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.17/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.17/0.49  thf('6', plain,
% 0.17/0.49      (~ (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.17/0.49          (k1_zfmisc_1 @ sk_C))),
% 0.17/0.49      inference('demod', [status(thm)], ['0', '5'])).
% 0.17/0.49  thf('7', plain,
% 0.17/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf(redefinition_k9_subset_1, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i]:
% 0.17/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.17/0.49       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.17/0.49  thf('8', plain,
% 0.17/0.49      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.17/0.49         (((k9_subset_1 @ X52 @ X50 @ X51) = (k3_xboole_0 @ X50 @ X51))
% 0.17/0.49          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52)))),
% 0.17/0.49      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.17/0.49  thf('9', plain,
% 0.17/0.49      (![X0 : $i]:
% 0.17/0.49         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.17/0.49           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.17/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.17/0.49  thf('10', plain,
% 0.17/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf(commutativity_k9_subset_1, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i]:
% 0.17/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.17/0.49       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.17/0.49  thf('11', plain,
% 0.17/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.17/0.49         (((k9_subset_1 @ X27 @ X29 @ X28) = (k9_subset_1 @ X27 @ X28 @ X29))
% 0.17/0.49          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.17/0.49      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.17/0.49  thf('12', plain,
% 0.17/0.49      (![X0 : $i]:
% 0.17/0.49         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.17/0.49           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.17/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.17/0.49  thf('13', plain,
% 0.17/0.49      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.17/0.49         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.17/0.49      inference('sup+', [status(thm)], ['9', '12'])).
% 0.17/0.49  thf('14', plain,
% 0.17/0.49      (~ (m1_subset_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ (k1_zfmisc_1 @ sk_C))),
% 0.17/0.49      inference('demod', [status(thm)], ['6', '13'])).
% 0.17/0.49  thf('15', plain,
% 0.17/0.49      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.17/0.49         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.17/0.49      inference('sup+', [status(thm)], ['9', '12'])).
% 0.17/0.49  thf('16', plain,
% 0.17/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.49  thf('17', plain,
% 0.17/0.49      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.17/0.49         (((k9_subset_1 @ X52 @ X50 @ X51) = (k3_xboole_0 @ X50 @ X51))
% 0.17/0.49          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52)))),
% 0.17/0.49      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.17/0.49  thf('18', plain,
% 0.17/0.49      (![X0 : $i]:
% 0.17/0.49         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.17/0.49           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.17/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.17/0.49  thf('19', plain,
% 0.17/0.49      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.17/0.49      inference('demod', [status(thm)], ['15', '18'])).
% 0.17/0.49  thf('20', plain,
% 0.17/0.49      (~ (m1_subset_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_C))),
% 0.17/0.49      inference('demod', [status(thm)], ['14', '19'])).
% 0.17/0.49  thf('21', plain,
% 0.17/0.49      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.17/0.49      inference('demod', [status(thm)], ['15', '18'])).
% 0.17/0.49  thf(t70_enumset1, axiom,
% 0.17/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.17/0.49  thf('22', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i]:
% 0.17/0.49         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.17/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.17/0.49  thf(t71_enumset1, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i]:
% 0.17/0.49     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.17/0.49  thf('23', plain,
% 0.17/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.49         ((k2_enumset1 @ X2 @ X2 @ X3 @ X4) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 0.17/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.17/0.49  thf(t72_enumset1, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.49     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.17/0.49  thf('24', plain,
% 0.17/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.17/0.49         ((k3_enumset1 @ X5 @ X5 @ X6 @ X7 @ X8)
% 0.17/0.49           = (k2_enumset1 @ X5 @ X6 @ X7 @ X8))),
% 0.17/0.49      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.17/0.49  thf(t73_enumset1, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.17/0.49     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.17/0.49       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.17/0.49  thf('25', plain,
% 0.17/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.17/0.49         ((k4_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.17/0.49           = (k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13))),
% 0.17/0.49      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.17/0.49  thf(t75_enumset1, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.17/0.49     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.17/0.49       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.17/0.49  thf('26', plain,
% 0.17/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.17/0.49         ((k6_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.17/0.49           = (k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.17/0.49      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.17/0.49  thf(t81_enumset1, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.17/0.49     ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 0.17/0.49       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.17/0.49  thf('27', plain,
% 0.17/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.17/0.49         ((k6_enumset1 @ X21 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.17/0.49           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 0.17/0.49      inference('cnf', [status(esa)], [t81_enumset1])).
% 0.17/0.49  thf('28', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.17/0.49         ((k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.17/0.49           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.17/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.17/0.49  thf(d5_enumset1, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.17/0.49     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.17/0.49       ( ![I:$i]:
% 0.17/0.49         ( ( r2_hidden @ I @ H ) <=>
% 0.17/0.49           ( ~( ( ( I ) != ( G ) ) & ( ( I ) != ( F ) ) & ( ( I ) != ( E ) ) & 
% 0.17/0.49                ( ( I ) != ( D ) ) & ( ( I ) != ( C ) ) & ( ( I ) != ( B ) ) & 
% 0.17/0.49                ( ( I ) != ( A ) ) ) ) ) ) ))).
% 0.17/0.49  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.17/0.49      $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.17/0.49  thf(zf_stmt_2, axiom,
% 0.17/0.49    (![I:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.17/0.49     ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.17/0.49       ( ( ( I ) != ( A ) ) & ( ( I ) != ( B ) ) & ( ( I ) != ( C ) ) & 
% 0.17/0.49         ( ( I ) != ( D ) ) & ( ( I ) != ( E ) ) & ( ( I ) != ( F ) ) & 
% 0.17/0.49         ( ( I ) != ( G ) ) ) ))).
% 0.17/0.49  thf(zf_stmt_3, axiom,
% 0.17/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.17/0.49     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.17/0.49       ( ![I:$i]:
% 0.17/0.49         ( ( r2_hidden @ I @ H ) <=>
% 0.17/0.49           ( ~( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.17/0.49  thf('29', plain,
% 0.17/0.49      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 0.17/0.49         X46 : $i, X47 : $i]:
% 0.17/0.49         ((zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.17/0.49          | (r2_hidden @ X39 @ X47)
% 0.17/0.49          | ((X47) != (k5_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40)))),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.17/0.49  thf('30', plain,
% 0.17/0.49      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 0.17/0.49         X46 : $i]:
% 0.17/0.49         ((r2_hidden @ X39 @ 
% 0.17/0.49           (k5_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40))
% 0.17/0.49          | (zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 0.17/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.17/0.49  thf('31', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.17/0.49         ((r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.17/0.49          | (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5))),
% 0.17/0.49      inference('sup+', [status(thm)], ['28', '30'])).
% 0.17/0.49  thf('32', plain,
% 0.17/0.49      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, 
% 0.17/0.49         X37 : $i]:
% 0.17/0.49         (((X31) != (X30))
% 0.17/0.49          | ~ (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X30))),
% 0.17/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.17/0.49  thf('33', plain,
% 0.17/0.49      (![X30 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.17/0.49         ~ (zip_tseitin_0 @ X30 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X30)),
% 0.17/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.17/0.49  thf('34', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.17/0.49         (r2_hidden @ X0 @ (k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5))),
% 0.17/0.49      inference('sup-', [status(thm)], ['31', '33'])).
% 0.17/0.49  thf('35', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.49         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.17/0.49      inference('sup+', [status(thm)], ['25', '34'])).
% 0.17/0.49  thf('36', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.49         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.17/0.49      inference('sup+', [status(thm)], ['24', '35'])).
% 0.17/0.49  thf('37', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.49         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.17/0.49      inference('sup+', [status(thm)], ['23', '36'])).
% 0.17/0.49  thf('38', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.17/0.49      inference('sup+', [status(thm)], ['22', '37'])).
% 0.17/0.49  thf(t4_setfam_1, axiom,
% 0.17/0.49    (![A:$i,B:$i]:
% 0.17/0.49     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.17/0.49  thf('39', plain,
% 0.17/0.49      (![X58 : $i, X59 : $i]:
% 0.17/0.49         ((r1_tarski @ (k1_setfam_1 @ X58) @ X59) | ~ (r2_hidden @ X59 @ X58))),
% 0.17/0.49      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.17/0.49  thf('40', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i]:
% 0.17/0.49         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 0.17/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.17/0.49  thf(t12_setfam_1, axiom,
% 0.17/0.49    (![A:$i,B:$i]:
% 0.17/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.17/0.49  thf('41', plain,
% 0.17/0.49      (![X53 : $i, X54 : $i]:
% 0.17/0.49         ((k1_setfam_1 @ (k2_tarski @ X53 @ X54)) = (k3_xboole_0 @ X53 @ X54))),
% 0.17/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.17/0.49  thf('42', plain,
% 0.17/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.17/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.17/0.49  thf('43', plain, ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_C)),
% 0.17/0.49      inference('sup+', [status(thm)], ['21', '42'])).
% 0.17/0.49  thf(t3_subset, axiom,
% 0.17/0.49    (![A:$i,B:$i]:
% 0.17/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.17/0.49  thf('44', plain,
% 0.17/0.49      (![X55 : $i, X57 : $i]:
% 0.17/0.49         ((m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X57)) | ~ (r1_tarski @ X55 @ X57))),
% 0.17/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.17/0.49  thf('45', plain,
% 0.17/0.49      ((m1_subset_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_C))),
% 0.17/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.17/0.49  thf('46', plain, ($false), inference('demod', [status(thm)], ['20', '45'])).
% 0.17/0.49  
% 0.17/0.49  % SZS output end Refutation
% 0.17/0.49  
% 0.17/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
