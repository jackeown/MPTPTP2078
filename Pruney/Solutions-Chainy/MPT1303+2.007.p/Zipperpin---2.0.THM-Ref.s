%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Jz2Gc9dmz

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:19 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 105 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  447 ( 984 expanded)
%              Number of equality atoms :   13 (  36 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t21_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v1_tops_2 @ B @ A )
               => ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v1_tops_2 @ B @ A )
                 => ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_tops_2])).

thf('0',plain,(
    ~ ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k9_subset_1 @ X38 @ X36 @ X37 )
        = ( k3_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k9_subset_1 @ X38 @ X36 @ X37 )
        = ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v1_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X41: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( r1_tarski @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k9_subset_1 @ X38 @ X36 @ X37 )
        = ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('19',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X5 ) ) @ X4 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X41: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( r1_tarski @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf(t18_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) )
      | ( v1_tops_2 @ X44 @ X45 )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ~ ( v1_tops_2 @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ X0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k9_subset_1 @ X0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ X0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k9_subset_1 @ X0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k9_subset_1 @ X0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ X0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X5 ) ) @ X4 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k9_subset_1 @ X0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A ) ),
    inference('sup+',[status(thm)],['12','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['6','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Jz2Gc9dmz
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.77  % Solved by: fo/fo7.sh
% 0.57/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.77  % done 499 iterations in 0.323s
% 0.57/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.77  % SZS output start Refutation
% 0.57/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.77  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.57/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.57/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.77  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.57/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.57/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.77  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.57/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.77  thf(t21_tops_2, conjecture,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( l1_pre_topc @ A ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( m1_subset_1 @
% 0.57/0.77             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.77           ( ![C:$i]:
% 0.57/0.77             ( ( m1_subset_1 @
% 0.57/0.77                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.77               ( ( v1_tops_2 @ B @ A ) =>
% 0.57/0.77                 ( v1_tops_2 @
% 0.57/0.77                   ( k9_subset_1 @
% 0.57/0.77                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.57/0.77                   A ) ) ) ) ) ) ))).
% 0.57/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.77    (~( ![A:$i]:
% 0.57/0.77        ( ( l1_pre_topc @ A ) =>
% 0.57/0.77          ( ![B:$i]:
% 0.57/0.77            ( ( m1_subset_1 @
% 0.57/0.77                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.77              ( ![C:$i]:
% 0.57/0.77                ( ( m1_subset_1 @
% 0.57/0.77                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.77                  ( ( v1_tops_2 @ B @ A ) =>
% 0.57/0.77                    ( v1_tops_2 @
% 0.57/0.77                      ( k9_subset_1 @
% 0.57/0.77                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.57/0.77                      A ) ) ) ) ) ) ) )),
% 0.57/0.77    inference('cnf.neg', [status(esa)], [t21_tops_2])).
% 0.57/0.77  thf('0', plain,
% 0.57/0.77      (~ (v1_tops_2 @ 
% 0.57/0.77          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.57/0.77          sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('1', plain,
% 0.57/0.77      ((m1_subset_1 @ sk_C @ 
% 0.57/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(redefinition_k9_subset_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.77       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.57/0.77  thf('2', plain,
% 0.57/0.77      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.57/0.77         (((k9_subset_1 @ X38 @ X36 @ X37) = (k3_xboole_0 @ X36 @ X37))
% 0.57/0.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.57/0.77      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.57/0.77  thf(t12_setfam_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.77  thf('3', plain,
% 0.57/0.77      (![X39 : $i, X40 : $i]:
% 0.57/0.77         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.57/0.77      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.57/0.77  thf('4', plain,
% 0.57/0.77      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.57/0.77         (((k9_subset_1 @ X38 @ X36 @ X37)
% 0.57/0.77            = (k1_setfam_1 @ (k2_tarski @ X36 @ X37)))
% 0.57/0.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.57/0.77      inference('demod', [status(thm)], ['2', '3'])).
% 0.57/0.77  thf('5', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.57/0.77           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['1', '4'])).
% 0.57/0.77  thf('6', plain,
% 0.57/0.77      (~ (v1_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.57/0.77      inference('demod', [status(thm)], ['0', '5'])).
% 0.57/0.77  thf(d10_xboole_0, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.77  thf('7', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.57/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.77  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.57/0.77      inference('simplify', [status(thm)], ['7'])).
% 0.57/0.77  thf(t3_subset, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.77  thf('9', plain,
% 0.57/0.77      (![X41 : $i, X43 : $i]:
% 0.57/0.77         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X43)) | ~ (r1_tarski @ X41 @ X43))),
% 0.57/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.77  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['8', '9'])).
% 0.57/0.77  thf('11', plain,
% 0.57/0.77      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.57/0.77         (((k9_subset_1 @ X38 @ X36 @ X37)
% 0.57/0.77            = (k1_setfam_1 @ (k2_tarski @ X36 @ X37)))
% 0.57/0.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.57/0.77      inference('demod', [status(thm)], ['2', '3'])).
% 0.57/0.77  thf('12', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.57/0.77  thf('13', plain,
% 0.57/0.77      ((m1_subset_1 @ sk_B @ 
% 0.57/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('14', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.57/0.77  thf('15', plain,
% 0.57/0.77      ((m1_subset_1 @ sk_B @ 
% 0.57/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('16', plain,
% 0.57/0.77      (![X41 : $i, X42 : $i]:
% 0.57/0.77         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.77  thf('17', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.57/0.77  thf(t108_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.57/0.77  thf('18', plain,
% 0.57/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 0.57/0.77      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.57/0.77  thf('19', plain,
% 0.57/0.77      (![X39 : $i, X40 : $i]:
% 0.57/0.77         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.57/0.77      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.57/0.77  thf('20', plain,
% 0.57/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X3 @ X4)
% 0.57/0.77          | (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X5)) @ X4))),
% 0.57/0.77      inference('demod', [status(thm)], ['18', '19'])).
% 0.57/0.77  thf('21', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ 
% 0.57/0.77          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['17', '20'])).
% 0.57/0.77  thf('22', plain,
% 0.57/0.77      (![X41 : $i, X43 : $i]:
% 0.57/0.77         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X43)) | ~ (r1_tarski @ X41 @ X43))),
% 0.57/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.77  thf('23', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ 
% 0.57/0.77          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['21', '22'])).
% 0.57/0.77  thf('24', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (m1_subset_1 @ (k9_subset_1 @ X0 @ sk_B @ X0) @ 
% 0.57/0.77          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.57/0.77      inference('sup+', [status(thm)], ['14', '23'])).
% 0.57/0.77  thf(t18_tops_2, axiom,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( l1_pre_topc @ A ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( m1_subset_1 @
% 0.57/0.77             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.77           ( ![C:$i]:
% 0.57/0.77             ( ( m1_subset_1 @
% 0.57/0.77                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.77               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.57/0.77                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.57/0.77  thf('25', plain,
% 0.57/0.77      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X44 @ 
% 0.57/0.77             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45))))
% 0.57/0.77          | (v1_tops_2 @ X44 @ X45)
% 0.57/0.77          | ~ (r1_tarski @ X44 @ X46)
% 0.57/0.77          | ~ (v1_tops_2 @ X46 @ X45)
% 0.57/0.77          | ~ (m1_subset_1 @ X46 @ 
% 0.57/0.77               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45))))
% 0.57/0.77          | ~ (l1_pre_topc @ X45))),
% 0.57/0.77      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.57/0.77  thf('26', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (~ (l1_pre_topc @ sk_A)
% 0.57/0.77          | ~ (m1_subset_1 @ X1 @ 
% 0.57/0.77               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.57/0.77          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.57/0.77          | ~ (r1_tarski @ (k9_subset_1 @ X0 @ sk_B @ X0) @ X1)
% 0.57/0.77          | (v1_tops_2 @ (k9_subset_1 @ X0 @ sk_B @ X0) @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['24', '25'])).
% 0.57/0.77  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('28', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X1 @ 
% 0.57/0.77             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.57/0.77          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.57/0.77          | ~ (r1_tarski @ (k9_subset_1 @ X0 @ sk_B @ X0) @ X1)
% 0.57/0.77          | (v1_tops_2 @ (k9_subset_1 @ X0 @ sk_B @ X0) @ sk_A))),
% 0.57/0.77      inference('demod', [status(thm)], ['26', '27'])).
% 0.57/0.77  thf('29', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((v1_tops_2 @ (k9_subset_1 @ X0 @ sk_B @ X0) @ sk_A)
% 0.57/0.77          | ~ (r1_tarski @ (k9_subset_1 @ X0 @ sk_B @ X0) @ sk_B)
% 0.57/0.77          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['13', '28'])).
% 0.57/0.77  thf('30', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.57/0.77  thf('31', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.57/0.77      inference('simplify', [status(thm)], ['7'])).
% 0.57/0.77  thf('32', plain,
% 0.57/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X3 @ X4)
% 0.57/0.77          | (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X5)) @ X4))),
% 0.57/0.77      inference('demod', [status(thm)], ['18', '19'])).
% 0.57/0.77  thf('33', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.57/0.77      inference('sup-', [status(thm)], ['31', '32'])).
% 0.57/0.77  thf('34', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X1)),
% 0.57/0.77      inference('sup+', [status(thm)], ['30', '33'])).
% 0.57/0.77  thf('35', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('36', plain,
% 0.57/0.77      (![X0 : $i]: (v1_tops_2 @ (k9_subset_1 @ X0 @ sk_B @ X0) @ sk_A)),
% 0.57/0.77      inference('demod', [status(thm)], ['29', '34', '35'])).
% 0.57/0.77  thf('37', plain,
% 0.57/0.77      (![X0 : $i]: (v1_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A)),
% 0.57/0.77      inference('sup+', [status(thm)], ['12', '36'])).
% 0.57/0.77  thf('38', plain, ($false), inference('demod', [status(thm)], ['6', '37'])).
% 0.57/0.77  
% 0.57/0.77  % SZS output end Refutation
% 0.57/0.77  
% 0.57/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
