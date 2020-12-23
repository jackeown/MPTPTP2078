%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JdFQ0uFpnc

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:22 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  513 ( 956 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t22_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v1_tops_2 @ B @ A )
               => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v1_tops_2 @ B @ A )
                 => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_tops_2])).

thf('0',plain,(
    ~ ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X14 @ X12 )
        = ( k9_subset_1 @ X13 @ X14 @ ( k3_subset_1 @ X13 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
        = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
        = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,
    ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

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

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_tops_2 @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ~ ( v1_tops_2 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 )
      | ( v1_tops_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 )
      | ( v1_tops_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( v1_tops_2 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('33',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup+',[status(thm)],['11','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JdFQ0uFpnc
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.02  % Solved by: fo/fo7.sh
% 0.82/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.02  % done 712 iterations in 0.556s
% 0.82/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.02  % SZS output start Refutation
% 0.82/1.02  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.82/1.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.82/1.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.02  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.82/1.02  thf(sk_C_type, type, sk_C: $i).
% 0.82/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.82/1.02  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.82/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.02  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.82/1.02  thf(t22_tops_2, conjecture,
% 0.82/1.02    (![A:$i]:
% 0.82/1.02     ( ( l1_pre_topc @ A ) =>
% 0.82/1.02       ( ![B:$i]:
% 0.82/1.02         ( ( m1_subset_1 @
% 0.82/1.02             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.02           ( ![C:$i]:
% 0.82/1.02             ( ( m1_subset_1 @
% 0.82/1.02                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.02               ( ( v1_tops_2 @ B @ A ) =>
% 0.82/1.02                 ( v1_tops_2 @
% 0.82/1.02                   ( k7_subset_1 @
% 0.82/1.02                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.82/1.02                   A ) ) ) ) ) ) ))).
% 0.82/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.02    (~( ![A:$i]:
% 0.82/1.02        ( ( l1_pre_topc @ A ) =>
% 0.82/1.02          ( ![B:$i]:
% 0.82/1.02            ( ( m1_subset_1 @
% 0.82/1.02                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.02              ( ![C:$i]:
% 0.82/1.02                ( ( m1_subset_1 @
% 0.82/1.02                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.02                  ( ( v1_tops_2 @ B @ A ) =>
% 0.82/1.02                    ( v1_tops_2 @
% 0.82/1.02                      ( k7_subset_1 @
% 0.82/1.02                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.82/1.02                      A ) ) ) ) ) ) ) )),
% 0.82/1.02    inference('cnf.neg', [status(esa)], [t22_tops_2])).
% 0.82/1.02  thf('0', plain,
% 0.82/1.02      (~ (v1_tops_2 @ 
% 0.82/1.02          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.82/1.02          sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('1', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_B @ 
% 0.82/1.02        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('2', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_C @ 
% 0.82/1.02        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf(t32_subset_1, axiom,
% 0.82/1.02    (![A:$i,B:$i]:
% 0.82/1.02     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.02       ( ![C:$i]:
% 0.82/1.02         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.02           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.82/1.02             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.82/1.02  thf('3', plain,
% 0.82/1.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.82/1.02          | ((k7_subset_1 @ X13 @ X14 @ X12)
% 0.82/1.02              = (k9_subset_1 @ X13 @ X14 @ (k3_subset_1 @ X13 @ X12)))
% 0.82/1.02          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.82/1.02      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.82/1.02  thf('4', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X0 @ 
% 0.82/1.02             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.82/1.02          | ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.82/1.02              = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ 
% 0.82/1.02                 (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))))),
% 0.82/1.02      inference('sup-', [status(thm)], ['2', '3'])).
% 0.82/1.02  thf('5', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_C @ 
% 0.82/1.02        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf(dt_k3_subset_1, axiom,
% 0.82/1.02    (![A:$i,B:$i]:
% 0.82/1.02     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.02       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.82/1.02  thf('6', plain,
% 0.82/1.02      (![X4 : $i, X5 : $i]:
% 0.82/1.02         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.82/1.02          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.82/1.02      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.82/1.02  thf('7', plain,
% 0.82/1.02      ((m1_subset_1 @ 
% 0.82/1.02        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C) @ 
% 0.82/1.02        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.82/1.02      inference('sup-', [status(thm)], ['5', '6'])).
% 0.82/1.02  thf(redefinition_k9_subset_1, axiom,
% 0.82/1.02    (![A:$i,B:$i,C:$i]:
% 0.82/1.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.02       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.82/1.02  thf('8', plain,
% 0.82/1.02      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.82/1.02         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.82/1.02          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.82/1.02      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.82/1.02  thf('9', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ 
% 0.82/1.02           (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))
% 0.82/1.02           = (k3_xboole_0 @ X0 @ 
% 0.82/1.02              (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['7', '8'])).
% 0.82/1.02  thf('10', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X0 @ 
% 0.82/1.02             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.82/1.02          | ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.82/1.02              = (k3_xboole_0 @ X0 @ 
% 0.82/1.02                 (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))))),
% 0.82/1.02      inference('demod', [status(thm)], ['4', '9'])).
% 0.82/1.02  thf('11', plain,
% 0.82/1.02      (((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)
% 0.82/1.02         = (k3_xboole_0 @ sk_B @ 
% 0.82/1.02            (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['1', '10'])).
% 0.82/1.02  thf(t17_xboole_1, axiom,
% 0.82/1.02    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.82/1.02  thf('12', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.82/1.02      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.82/1.02  thf(t28_xboole_1, axiom,
% 0.82/1.02    (![A:$i,B:$i]:
% 0.82/1.02     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.82/1.02  thf('13', plain,
% 0.82/1.02      (![X2 : $i, X3 : $i]:
% 0.82/1.02         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.82/1.02      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.82/1.02  thf('14', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.82/1.02           = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.02      inference('sup-', [status(thm)], ['12', '13'])).
% 0.82/1.02  thf('15', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_B @ 
% 0.82/1.02        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('16', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_B @ 
% 0.82/1.02        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf(dt_k9_subset_1, axiom,
% 0.82/1.02    (![A:$i,B:$i,C:$i]:
% 0.82/1.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.82/1.02       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.82/1.02  thf('17', plain,
% 0.82/1.02      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.02         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.82/1.02          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.82/1.02      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.82/1.02  thf('18', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (m1_subset_1 @ 
% 0.82/1.02          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 0.82/1.02          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.82/1.02      inference('sup-', [status(thm)], ['16', '17'])).
% 0.82/1.02  thf('19', plain,
% 0.82/1.02      ((m1_subset_1 @ sk_B @ 
% 0.82/1.02        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('20', plain,
% 0.82/1.02      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.82/1.02         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.82/1.02          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.82/1.02      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.82/1.02  thf('21', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.82/1.02           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.82/1.02      inference('sup-', [status(thm)], ['19', '20'])).
% 0.82/1.02  thf('22', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.82/1.02          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.82/1.02      inference('demod', [status(thm)], ['18', '21'])).
% 0.82/1.02  thf(t18_tops_2, axiom,
% 0.82/1.02    (![A:$i]:
% 0.82/1.02     ( ( l1_pre_topc @ A ) =>
% 0.82/1.02       ( ![B:$i]:
% 0.82/1.02         ( ( m1_subset_1 @
% 0.82/1.02             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.02           ( ![C:$i]:
% 0.82/1.02             ( ( m1_subset_1 @
% 0.82/1.02                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.82/1.02               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.82/1.02                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.82/1.02  thf('23', plain,
% 0.82/1.02      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X15 @ 
% 0.82/1.02             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.82/1.02          | (v1_tops_2 @ X15 @ X16)
% 0.82/1.02          | ~ (r1_tarski @ X15 @ X17)
% 0.82/1.02          | ~ (v1_tops_2 @ X17 @ X16)
% 0.82/1.02          | ~ (m1_subset_1 @ X17 @ 
% 0.82/1.02               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.82/1.02          | ~ (l1_pre_topc @ X16))),
% 0.82/1.02      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.82/1.02  thf('24', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         (~ (l1_pre_topc @ sk_A)
% 0.82/1.02          | ~ (m1_subset_1 @ X1 @ 
% 0.82/1.02               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.82/1.02          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.82/1.02          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1)
% 0.82/1.02          | (v1_tops_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.82/1.02      inference('sup-', [status(thm)], ['22', '23'])).
% 0.82/1.02  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('26', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         (~ (m1_subset_1 @ X1 @ 
% 0.82/1.02             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.82/1.02          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.82/1.02          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1)
% 0.82/1.02          | (v1_tops_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.82/1.02      inference('demod', [status(thm)], ['24', '25'])).
% 0.82/1.02  thf('27', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((v1_tops_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.82/1.02          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 0.82/1.02          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.82/1.02      inference('sup-', [status(thm)], ['15', '26'])).
% 0.82/1.02  thf('28', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('29', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((v1_tops_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.82/1.02          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B))),
% 0.82/1.02      inference('demod', [status(thm)], ['27', '28'])).
% 0.82/1.02  thf('30', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.82/1.02          | (v1_tops_2 @ (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_B) @ 
% 0.82/1.02             sk_A))),
% 0.82/1.02      inference('sup-', [status(thm)], ['14', '29'])).
% 0.82/1.02  thf('31', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.82/1.02      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.82/1.02  thf('32', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.82/1.02           = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.02      inference('sup-', [status(thm)], ['12', '13'])).
% 0.82/1.02  thf('33', plain,
% 0.82/1.02      (![X0 : $i]: (v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.82/1.02      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.82/1.02  thf('34', plain,
% 0.82/1.02      ((v1_tops_2 @ 
% 0.82/1.02        (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.82/1.02        sk_A)),
% 0.82/1.02      inference('sup+', [status(thm)], ['11', '33'])).
% 0.82/1.02  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.82/1.02  
% 0.82/1.02  % SZS output end Refutation
% 0.82/1.02  
% 0.82/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
