%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.boJpI4o4n5

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 237 expanded)
%              Number of leaves         :   28 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  558 (2552 expanded)
%              Number of equality atoms :   34 ( 130 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t33_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v3_pre_topc @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                     => ( ( D = B )
                       => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tops_2])).

thf('0',plain,(
    ~ ( v3_pre_topc @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( k2_struct_0 @ sk_C ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_C ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_C ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['18','25'])).

thf(t32_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v3_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X22 @ ( k2_struct_0 @ X19 ) )
       != X21 )
      | ~ ( v3_pre_topc @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_pre_topc @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('28',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X22 @ ( k2_struct_0 @ X19 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X22 @ ( k2_struct_0 @ X19 ) ) @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_C ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_B @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['29','34','43','44','45','46','47'])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['2','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.boJpI4o4n5
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:23:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 95 iterations in 0.042s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(t33_tops_2, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.49               ( ( v3_pre_topc @ B @ A ) =>
% 0.19/0.49                 ( ![D:$i]:
% 0.19/0.49                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.19/0.49                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( l1_pre_topc @ A ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49              ( ![C:$i]:
% 0.19/0.49                ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.49                  ( ( v3_pre_topc @ B @ A ) =>
% 0.19/0.49                    ( ![D:$i]:
% 0.19/0.49                      ( ( m1_subset_1 @
% 0.19/0.49                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.19/0.49                        ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t33_tops_2])).
% 0.19/0.49  thf('0', plain, (~ (v3_pre_topc @ sk_D_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain, (((sk_D_1) = (sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('2', plain, (~ (v3_pre_topc @ sk_B @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d3_struct_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X15 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('6', plain, (((sk_D_1) = (sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf(commutativity_k9_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.49         (((k9_subset_1 @ X4 @ X6 @ X5) = (k9_subset_1 @ X4 @ X5 @ X6))
% 0.19/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k9_subset_1 @ (u1_struct_0 @ sk_C) @ X0 @ sk_B)
% 0.19/0.49           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k9_subset_1 @ (k2_struct_0 @ sk_C) @ X0 @ sk_B)
% 0.19/0.49            = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))
% 0.19/0.49          | ~ (l1_struct_0 @ sk_C))),
% 0.19/0.49      inference('sup+', [status(thm)], ['4', '9'])).
% 0.19/0.49  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_m1_pre_topc, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X17 @ X18)
% 0.19/0.49          | (l1_pre_topc @ X17)
% 0.19/0.49          | ~ (l1_pre_topc @ X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.49  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('15', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf(dt_l1_pre_topc, axiom,
% 0.19/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('17', plain, ((l1_struct_0 @ sk_C)),
% 0.19/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k9_subset_1 @ (k2_struct_0 @ sk_C) @ X0 @ sk_B)
% 0.19/0.49           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['10', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X15 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_C))),
% 0.19/0.49      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain, ((l1_struct_0 @ sk_C)),
% 0.19/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.49  thf(redefinition_k9_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.19/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k9_subset_1 @ (k2_struct_0 @ sk_C) @ X0 @ sk_B)
% 0.19/0.49           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k3_xboole_0 @ X0 @ sk_B)
% 0.19/0.49           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['18', '25'])).
% 0.19/0.49  thf(t32_tops_2, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.49               ( ( v3_pre_topc @ C @ B ) <=>
% 0.19/0.49                 ( ?[D:$i]:
% 0.19/0.49                   ( ( ( k9_subset_1 @
% 0.19/0.49                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.19/0.49                       ( C ) ) & 
% 0.19/0.49                     ( v3_pre_topc @ D @ A ) & 
% 0.19/0.49                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X19 @ X20)
% 0.19/0.49          | ((k9_subset_1 @ (u1_struct_0 @ X19) @ X22 @ (k2_struct_0 @ X19))
% 0.19/0.49              != (X21))
% 0.19/0.49          | ~ (v3_pre_topc @ X22 @ X20)
% 0.19/0.49          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.49          | (v3_pre_topc @ X21 @ X19)
% 0.19/0.49          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.49          | ~ (l1_pre_topc @ X20))),
% 0.19/0.49      inference('cnf', [status(esa)], [t32_tops_2])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.19/0.49         (~ (l1_pre_topc @ X20)
% 0.19/0.49          | ~ (m1_subset_1 @ 
% 0.19/0.49               (k9_subset_1 @ (u1_struct_0 @ X19) @ X22 @ (k2_struct_0 @ X19)) @ 
% 0.19/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.49          | (v3_pre_topc @ 
% 0.19/0.49             (k9_subset_1 @ (u1_struct_0 @ X19) @ X22 @ (k2_struct_0 @ X19)) @ 
% 0.19/0.49             X19)
% 0.19/0.49          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.49          | ~ (v3_pre_topc @ X22 @ X20)
% 0.19/0.49          | ~ (m1_pre_topc @ X19 @ X20))),
% 0.19/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ (k3_xboole_0 @ (k2_struct_0 @ sk_C) @ sk_B) @ 
% 0.19/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.19/0.49          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.49          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.19/0.49          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.49          | (v3_pre_topc @ 
% 0.19/0.49             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.19/0.49             sk_C)
% 0.19/0.49          | ~ (l1_pre_topc @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['26', '28'])).
% 0.19/0.49  thf(commutativity_k2_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.49  thf(t12_setfam_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X15 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf(t3_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.49  thf('38', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf(t28_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.49  thf('40', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_C)) = (sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      ((((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) = (sk_B))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_C))),
% 0.19/0.49      inference('sup+', [status(thm)], ['35', '40'])).
% 0.19/0.49  thf('42', plain, ((l1_struct_0 @ sk_C)),
% 0.19/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('43', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) = (sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k3_xboole_0 @ X0 @ sk_B)
% 0.19/0.49           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['18', '25'])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('47', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) = (sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.49          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.19/0.49          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.49          | (v3_pre_topc @ sk_B @ sk_C)
% 0.19/0.49          | ~ (l1_pre_topc @ X0))),
% 0.19/0.49      inference('demod', [status(thm)],
% 0.19/0.49                ['29', '34', '43', '44', '45', '46', '47'])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.49        | (v3_pre_topc @ sk_B @ sk_C)
% 0.19/0.49        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.19/0.49        | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '48'])).
% 0.19/0.49  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('51', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('53', plain, ((v3_pre_topc @ sk_B @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.19/0.49  thf('54', plain, ($false), inference('demod', [status(thm)], ['2', '53'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
