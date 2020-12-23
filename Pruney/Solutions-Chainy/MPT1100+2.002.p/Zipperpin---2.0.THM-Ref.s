%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dDGCL5rWL0

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  64 expanded)
%              Number of leaves         :   38 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  305 ( 341 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X29: $i,X31: $i] :
      ( ~ ( v2_pre_topc @ X29 )
      | ( zip_tseitin_5 @ X31 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ( zip_tseitin_4 @ X26 @ X27 )
      | ~ ( zip_tseitin_5 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_5 @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_4 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_4 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ ( u1_pre_topc @ X24 ) )
      | ~ ( zip_tseitin_4 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k5_setfam_1 @ X3 @ X2 )
        = ( k3_tarski @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ k1_xboole_0 )
      = ( k3_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('11',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf(t5_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_pre_topc])).

thf('15',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['16','17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dDGCL5rWL0
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 44 iterations in 0.027s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.20/0.49  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.20/0.49  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.49  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(d1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.49         ( ( ![B:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49               ( ![C:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.49                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.49                     ( r2_hidden @
% 0.20/0.49                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.20/0.49                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.20/0.49           ( ![B:$i]:
% 0.20/0.49             ( ( m1_subset_1 @
% 0.20/0.49                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.49                 ( r2_hidden @
% 0.20/0.49                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.49                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.20/0.49           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_1, axiom,
% 0.20/0.49    (![B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.20/0.49       ( ( m1_subset_1 @
% 0.20/0.49           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.20/0.49  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_3, axiom,
% 0.20/0.49    (![B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.20/0.49       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.49         ( r2_hidden @
% 0.20/0.49           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_5, axiom,
% 0.20/0.49    (![B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.20/0.49       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_7, axiom,
% 0.20/0.49    (![C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.20/0.49       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.20/0.49  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_9, axiom,
% 0.20/0.49    (![C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.20/0.49       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.49         ( r2_hidden @
% 0.20/0.49           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_11, axiom,
% 0.20/0.49    (![C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.20/0.49       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.49         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_12, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.49         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.49           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.20/0.49           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X29 : $i, X31 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X29)
% 0.20/0.49          | (zip_tseitin_5 @ X31 @ X29)
% 0.20/0.49          | ~ (l1_pre_topc @ X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.20/0.49  thf(t4_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X26 : $i, X27 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X26 @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 0.20/0.49          | (zip_tseitin_4 @ X26 @ X27)
% 0.20/0.49          | ~ (zip_tseitin_5 @ X26 @ X27))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (zip_tseitin_5 @ k1_xboole_0 @ X0)
% 0.20/0.49          | (zip_tseitin_4 @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | (zip_tseitin_4 @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.49  thf('5', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.20/0.49          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X24) @ X23) @ 
% 0.20/0.49             (u1_pre_topc @ X24))
% 0.20/0.49          | ~ (zip_tseitin_4 @ X23 @ X24))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (zip_tseitin_4 @ k1_xboole_0 @ X0)
% 0.20/0.49          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.20/0.49             (u1_pre_topc @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf(redefinition_k5_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]:
% 0.20/0.49         (((k5_setfam_1 @ X3 @ X2) = (k3_tarski @ X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k5_setfam_1 @ X0 @ k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.49  thf('11', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]: ((k5_setfam_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (zip_tseitin_4 @ k1_xboole_0 @ X0)
% 0.20/0.49          | (r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '13'])).
% 0.20/0.50  thf(t5_pre_topc, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ))).
% 0.20/0.50  thf(zf_stmt_13, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t5_pre_topc])).
% 0.20/0.50  thf('15', plain, (~ (r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.50  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.50  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.50  thf('19', plain, ($false),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
