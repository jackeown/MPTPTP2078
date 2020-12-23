%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qtg5TllKXX

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:24 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 140 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  537 (1750 expanded)
%              Number of equality atoms :   19 (  49 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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

thf('15',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ( v2_tops_2 @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ~ ( v2_tops_2 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t19_tops_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) @ X1 )
      | ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) @ X1 )
      | ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 )
      | ( v2_tops_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_B )
    | ( v2_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','29'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('32',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('33',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('39',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('43',plain,(
    v2_tops_2 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['30','41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['14','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qtg5TllKXX
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:10:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 211 iterations in 0.111s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.55  thf(t24_tops_2, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @
% 0.37/0.55             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( m1_subset_1 @
% 0.37/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.55               ( ( v2_tops_2 @ B @ A ) =>
% 0.37/0.55                 ( v2_tops_2 @
% 0.37/0.55                   ( k9_subset_1 @
% 0.37/0.55                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.37/0.55                   A ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( l1_pre_topc @ A ) =>
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ( m1_subset_1 @
% 0.37/0.55                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.55              ( ![C:$i]:
% 0.37/0.55                ( ( m1_subset_1 @
% 0.37/0.55                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.55                  ( ( v2_tops_2 @ B @ A ) =>
% 0.37/0.55                    ( v2_tops_2 @
% 0.37/0.55                      ( k9_subset_1 @
% 0.37/0.55                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.37/0.55                      A ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t24_tops_2])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (~ (v2_tops_2 @ 
% 0.37/0.55          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.37/0.55          sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(redefinition_k9_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.37/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.37/0.55           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('4', plain, (~ (v2_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.37/0.55      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(commutativity_k9_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 0.37/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.37/0.55           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.37/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.37/0.55           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X0 @ sk_B)
% 0.37/0.55           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['7', '10'])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.37/0.55           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('14', plain, (~ (v2_tops_2 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A)),
% 0.37/0.55      inference('demod', [status(thm)], ['4', '13'])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_k9_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 0.37/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (m1_subset_1 @ 
% 0.37/0.55          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C) @ 
% 0.37/0.55          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.55  thf(t19_tops_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @
% 0.37/0.55             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( m1_subset_1 @
% 0.37/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.55               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.37/0.55                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X16 @ 
% 0.37/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.37/0.55          | (v2_tops_2 @ X16 @ X17)
% 0.37/0.55          | ~ (r1_tarski @ X16 @ X18)
% 0.37/0.55          | ~ (v2_tops_2 @ X18 @ X17)
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ 
% 0.37/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.37/0.55          | ~ (l1_pre_topc @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [t19_tops_2])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.37/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.37/0.55          | ~ (r1_tarski @ 
% 0.37/0.55               (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C) @ 
% 0.37/0.55               X1)
% 0.37/0.55          | (v2_tops_2 @ 
% 0.37/0.55             (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C) @ 
% 0.37/0.55             sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.37/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.37/0.55          | ~ (r1_tarski @ 
% 0.37/0.55               (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C) @ 
% 0.37/0.55               X1)
% 0.37/0.55          | (v2_tops_2 @ 
% 0.37/0.55             (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C) @ 
% 0.37/0.55             sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.37/0.55           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 0.37/0.55           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.37/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.37/0.55          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1)
% 0.37/0.55          | (v2_tops_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_tops_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.37/0.55          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_B)
% 0.37/0.55          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '26'])).
% 0.37/0.55  thf('28', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_tops_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.37/0.55          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((~ (r1_tarski @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_B)
% 0.37/0.55        | (v2_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '29'])).
% 0.37/0.55  thf(dt_k2_subset_1, axiom,
% 0.37/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.37/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.55  thf('32', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.55  thf('33', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.37/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 0.37/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf(t3_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i]:
% 0.37/0.55         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('38', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.37/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.37/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.37/0.55      inference('demod', [status(thm)], ['37', '40'])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('43', plain, ((v2_tops_2 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A)),
% 0.37/0.55      inference('demod', [status(thm)], ['30', '41', '42'])).
% 0.37/0.55  thf('44', plain, ($false), inference('demod', [status(thm)], ['14', '43'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
