%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g1oeU1OCtM

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:24 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   61 (  99 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  510 (1174 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t24_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v2_tops_2 @ B @ A )
               => ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v2_tops_2 @ B @ A )
                 => ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tops_2])).

thf('0',plain,(
    ~ ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k9_subset_1 @ X41 @ X39 @ X40 )
        = ( k3_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k9_subset_1 @ X33 @ X35 @ X34 )
        = ( k9_subset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k9_subset_1 @ X41 @ X39 @ X40 )
        = ( k3_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_tops_2 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['4','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X36 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t19_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) )
      | ( v2_tops_2 @ X48 @ X49 )
      | ~ ( r1_tarski @ X48 @ X50 )
      | ~ ( v2_tops_2 @ X50 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t19_tops_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ X1 )
      | ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ X1 )
      | ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 )
      | ( v2_tops_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X36 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k9_subset_1 @ X41 @ X39 @ X40 )
        = ( k3_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( v2_tops_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['14','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g1oeU1OCtM
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.51/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.68  % Solved by: fo/fo7.sh
% 0.51/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.68  % done 430 iterations in 0.253s
% 0.51/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.68  % SZS output start Refutation
% 0.51/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.68  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.51/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.68  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.51/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.68  thf(t24_tops_2, conjecture,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( l1_pre_topc @ A ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( m1_subset_1 @
% 0.51/0.68             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.68           ( ![C:$i]:
% 0.51/0.68             ( ( m1_subset_1 @
% 0.51/0.68                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.68               ( ( v2_tops_2 @ B @ A ) =>
% 0.51/0.68                 ( v2_tops_2 @
% 0.51/0.68                   ( k9_subset_1 @
% 0.51/0.68                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.51/0.68                   A ) ) ) ) ) ) ))).
% 0.51/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.68    (~( ![A:$i]:
% 0.51/0.68        ( ( l1_pre_topc @ A ) =>
% 0.51/0.68          ( ![B:$i]:
% 0.51/0.68            ( ( m1_subset_1 @
% 0.51/0.68                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.68              ( ![C:$i]:
% 0.51/0.68                ( ( m1_subset_1 @
% 0.51/0.68                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.68                  ( ( v2_tops_2 @ B @ A ) =>
% 0.51/0.68                    ( v2_tops_2 @
% 0.51/0.68                      ( k9_subset_1 @
% 0.51/0.68                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.51/0.68                      A ) ) ) ) ) ) ) )),
% 0.51/0.68    inference('cnf.neg', [status(esa)], [t24_tops_2])).
% 0.51/0.68  thf('0', plain,
% 0.51/0.68      (~ (v2_tops_2 @ 
% 0.51/0.68          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.51/0.68          sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('1', plain,
% 0.51/0.68      ((m1_subset_1 @ sk_C @ 
% 0.51/0.68        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(redefinition_k9_subset_1, axiom,
% 0.51/0.68    (![A:$i,B:$i,C:$i]:
% 0.51/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.68       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.51/0.68  thf('2', plain,
% 0.51/0.68      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.51/0.68         (((k9_subset_1 @ X41 @ X39 @ X40) = (k3_xboole_0 @ X39 @ X40))
% 0.51/0.68          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 0.51/0.68      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.51/0.68  thf('3', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.51/0.68           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.51/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.68  thf('4', plain, (~ (v2_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.51/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.51/0.68  thf('5', plain,
% 0.51/0.68      ((m1_subset_1 @ sk_B @ 
% 0.51/0.68        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(commutativity_k9_subset_1, axiom,
% 0.51/0.68    (![A:$i,B:$i,C:$i]:
% 0.51/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.68       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.51/0.68  thf('6', plain,
% 0.51/0.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.51/0.68         (((k9_subset_1 @ X33 @ X35 @ X34) = (k9_subset_1 @ X33 @ X34 @ X35))
% 0.51/0.68          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.51/0.68      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.51/0.68  thf('7', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.51/0.68           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.68  thf('8', plain,
% 0.51/0.68      ((m1_subset_1 @ sk_B @ 
% 0.51/0.68        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('9', plain,
% 0.51/0.68      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.51/0.68         (((k9_subset_1 @ X41 @ X39 @ X40) = (k3_xboole_0 @ X39 @ X40))
% 0.51/0.68          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 0.51/0.68      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.51/0.68  thf('10', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.51/0.68           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.51/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.68  thf('11', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((k3_xboole_0 @ X0 @ sk_B)
% 0.51/0.68           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))),
% 0.51/0.68      inference('demod', [status(thm)], ['7', '10'])).
% 0.51/0.68  thf('12', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.51/0.68           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.51/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.68  thf('13', plain,
% 0.51/0.68      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.51/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.51/0.68  thf('14', plain, (~ (v2_tops_2 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A)),
% 0.51/0.68      inference('demod', [status(thm)], ['4', '13'])).
% 0.51/0.68  thf('15', plain,
% 0.51/0.68      ((m1_subset_1 @ sk_B @ 
% 0.51/0.68        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('16', plain,
% 0.51/0.68      ((m1_subset_1 @ sk_B @ 
% 0.51/0.68        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(dt_k9_subset_1, axiom,
% 0.51/0.68    (![A:$i,B:$i,C:$i]:
% 0.51/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.68       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.68  thf('17', plain,
% 0.51/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.51/0.68         ((m1_subset_1 @ (k9_subset_1 @ X36 @ X37 @ X38) @ (k1_zfmisc_1 @ X36))
% 0.51/0.68          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X36)))),
% 0.51/0.68      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.51/0.68  thf('18', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (m1_subset_1 @ 
% 0.51/0.68          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 0.51/0.68          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.68  thf(t19_tops_2, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( l1_pre_topc @ A ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( m1_subset_1 @
% 0.51/0.68             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.68           ( ![C:$i]:
% 0.51/0.68             ( ( m1_subset_1 @
% 0.51/0.68                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.68               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.51/0.68                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.51/0.68  thf('19', plain,
% 0.51/0.68      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.51/0.68         (~ (m1_subset_1 @ X48 @ 
% 0.51/0.68             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))
% 0.51/0.68          | (v2_tops_2 @ X48 @ X49)
% 0.51/0.68          | ~ (r1_tarski @ X48 @ X50)
% 0.51/0.68          | ~ (v2_tops_2 @ X50 @ X49)
% 0.51/0.68          | ~ (m1_subset_1 @ X50 @ 
% 0.51/0.68               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))
% 0.51/0.68          | ~ (l1_pre_topc @ X49))),
% 0.51/0.68      inference('cnf', [status(esa)], [t19_tops_2])).
% 0.51/0.68  thf('20', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ sk_A)
% 0.51/0.68          | ~ (m1_subset_1 @ X1 @ 
% 0.51/0.68               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.51/0.68          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.51/0.68          | ~ (r1_tarski @ 
% 0.51/0.68               (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 0.51/0.68               X1)
% 0.51/0.68          | (v2_tops_2 @ 
% 0.51/0.68             (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 0.51/0.68             sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.51/0.68  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('22', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.51/0.68             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.51/0.68          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.51/0.68          | ~ (r1_tarski @ 
% 0.51/0.68               (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 0.51/0.68               X1)
% 0.51/0.68          | (v2_tops_2 @ 
% 0.51/0.68             (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 0.51/0.68             sk_A))),
% 0.51/0.68      inference('demod', [status(thm)], ['20', '21'])).
% 0.51/0.68  thf('23', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.51/0.68           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.51/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.68  thf('24', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.51/0.68           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.51/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.68  thf('25', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.51/0.68             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.51/0.68          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.51/0.68          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1)
% 0.51/0.68          | (v2_tops_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.51/0.68      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.51/0.68  thf('26', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((v2_tops_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.51/0.68          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 0.51/0.68          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['15', '25'])).
% 0.51/0.68  thf(d10_xboole_0, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.68  thf('27', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.51/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.68  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.51/0.68      inference('simplify', [status(thm)], ['27'])).
% 0.51/0.68  thf(t3_subset, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.68  thf('29', plain,
% 0.51/0.68      (![X44 : $i, X46 : $i]:
% 0.51/0.68         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 0.51/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.68  thf('30', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.68  thf('31', plain,
% 0.51/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.51/0.68         ((m1_subset_1 @ (k9_subset_1 @ X36 @ X37 @ X38) @ (k1_zfmisc_1 @ X36))
% 0.51/0.68          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X36)))),
% 0.51/0.68      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.51/0.68  thf('32', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.51/0.68  thf('33', plain,
% 0.51/0.68      (![X44 : $i, X45 : $i]:
% 0.51/0.68         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 0.51/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.68  thf('34', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.51/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.51/0.68  thf('35', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.68  thf('36', plain,
% 0.51/0.68      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.51/0.68         (((k9_subset_1 @ X41 @ X39 @ X40) = (k3_xboole_0 @ X39 @ X40))
% 0.51/0.68          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 0.51/0.68      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.51/0.68  thf('37', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.51/0.68  thf('38', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.51/0.68      inference('demod', [status(thm)], ['34', '37'])).
% 0.51/0.68  thf('39', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('40', plain,
% 0.51/0.68      (![X0 : $i]: (v2_tops_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.51/0.68      inference('demod', [status(thm)], ['26', '38', '39'])).
% 0.51/0.68  thf('41', plain, ($false), inference('demod', [status(thm)], ['14', '40'])).
% 0.51/0.68  
% 0.51/0.68  % SZS output end Refutation
% 0.51/0.68  
% 0.51/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
