%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9GnWtEahMG

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:31 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 185 expanded)
%              Number of leaves         :   31 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  559 (2028 expanded)
%              Number of equality atoms :   30 ( 102 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ~ ( v3_pre_topc @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X8 @ X10 @ X9 )
        = ( k9_subset_1 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

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

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_struct_0 @ X23 ) )
       != X25 )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_pre_topc @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('14',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_struct_0 @ X23 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_struct_0 @ X23 ) ) @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['21','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('38',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','39'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_B @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20','40','41','42','43','44'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_C_1 )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['2','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9GnWtEahMG
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 18:30:06 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 94 iterations in 0.046s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.23/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.23/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.23/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.52  thf(t33_tops_2, conjecture,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( l1_pre_topc @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.52           ( ![C:$i]:
% 0.23/0.52             ( ( m1_pre_topc @ C @ A ) =>
% 0.23/0.52               ( ( v3_pre_topc @ B @ A ) =>
% 0.23/0.52                 ( ![D:$i]:
% 0.23/0.52                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.23/0.52                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i]:
% 0.23/0.52        ( ( l1_pre_topc @ A ) =>
% 0.23/0.52          ( ![B:$i]:
% 0.23/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.52              ( ![C:$i]:
% 0.23/0.52                ( ( m1_pre_topc @ C @ A ) =>
% 0.23/0.52                  ( ( v3_pre_topc @ B @ A ) =>
% 0.23/0.52                    ( ![D:$i]:
% 0.23/0.52                      ( ( m1_subset_1 @
% 0.23/0.52                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.23/0.52                        ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t33_tops_2])).
% 0.23/0.52  thf('0', plain, (~ (v3_pre_topc @ sk_D_1 @ sk_C_1)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('1', plain, (((sk_D_1) = (sk_B))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('2', plain, (~ (v3_pre_topc @ sk_B @ sk_C_1)),
% 0.23/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('5', plain, (((sk_D_1) = (sk_B))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.23/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.52  thf(commutativity_k9_subset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.52         (((k9_subset_1 @ X8 @ X10 @ X9) = (k9_subset_1 @ X8 @ X9 @ X10))
% 0.23/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.23/0.52      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.23/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.52  thf('9', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.23/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.52  thf(redefinition_k9_subset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.23/0.52  thf('10', plain,
% 0.23/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.52         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.23/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.23/0.52           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((k3_xboole_0 @ X0 @ sk_B)
% 0.23/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.23/0.52      inference('demod', [status(thm)], ['8', '11'])).
% 0.23/0.52  thf(t32_tops_2, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( l1_pre_topc @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.52           ( ![C:$i]:
% 0.23/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.23/0.52               ( ( v3_pre_topc @ C @ B ) <=>
% 0.23/0.52                 ( ?[D:$i]:
% 0.23/0.52                   ( ( ( k9_subset_1 @
% 0.23/0.52                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.23/0.52                       ( C ) ) & 
% 0.23/0.52                     ( v3_pre_topc @ D @ A ) & 
% 0.23/0.52                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.23/0.52         (~ (m1_pre_topc @ X23 @ X24)
% 0.23/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X26 @ (k2_struct_0 @ X23))
% 0.23/0.52              != (X25))
% 0.23/0.52          | ~ (v3_pre_topc @ X26 @ X24)
% 0.23/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.23/0.52          | (v3_pre_topc @ X25 @ X23)
% 0.23/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.23/0.52          | ~ (l1_pre_topc @ X24))),
% 0.23/0.52      inference('cnf', [status(esa)], [t32_tops_2])).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.23/0.52         (~ (l1_pre_topc @ X24)
% 0.23/0.52          | ~ (m1_subset_1 @ 
% 0.23/0.52               (k9_subset_1 @ (u1_struct_0 @ X23) @ X26 @ (k2_struct_0 @ X23)) @ 
% 0.23/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.23/0.52          | (v3_pre_topc @ 
% 0.23/0.52             (k9_subset_1 @ (u1_struct_0 @ X23) @ X26 @ (k2_struct_0 @ X23)) @ 
% 0.23/0.52             X23)
% 0.23/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.23/0.52          | ~ (v3_pre_topc @ X26 @ X24)
% 0.23/0.52          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.23/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ (k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B) @ 
% 0.23/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.23/0.52          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.23/0.52          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.23/0.52          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.52          | (v3_pre_topc @ 
% 0.23/0.52             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 0.23/0.52              (k2_struct_0 @ sk_C_1)) @ 
% 0.23/0.52             sk_C_1)
% 0.23/0.52          | ~ (l1_pre_topc @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['12', '14'])).
% 0.23/0.52  thf(commutativity_k2_tarski, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.23/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.23/0.52  thf(t12_setfam_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      (![X17 : $i, X18 : $i]:
% 0.23/0.52         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.23/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      (![X17 : $i, X18 : $i]:
% 0.23/0.52         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.23/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.23/0.52  thf(d3_struct_0, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      (![X19 : $i]:
% 0.23/0.52         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.23/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.23/0.52  thf(d3_tarski, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      (![X1 : $i, X3 : $i]:
% 0.23/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.23/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.23/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.52  thf(l3_subset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.23/0.52  thf('24', plain,
% 0.23/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X11 @ X12)
% 0.23/0.52          | (r2_hidden @ X11 @ X13)
% 0.23/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.23/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.23/0.52  thf('25', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.52  thf('26', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r1_tarski @ sk_B @ X0)
% 0.23/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['22', '25'])).
% 0.23/0.52  thf('27', plain,
% 0.23/0.52      (![X1 : $i, X3 : $i]:
% 0.23/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.23/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.52  thf('28', plain,
% 0.23/0.52      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_C_1))
% 0.23/0.52        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_C_1)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.52  thf('29', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_C_1))),
% 0.23/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.23/0.52  thf(t28_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.52  thf('30', plain,
% 0.23/0.52      (![X4 : $i, X5 : $i]:
% 0.23/0.52         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.23/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.52  thf('31', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_C_1)) = (sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.23/0.52  thf('32', plain,
% 0.23/0.52      ((((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))
% 0.23/0.52        | ~ (l1_struct_0 @ sk_C_1))),
% 0.23/0.52      inference('sup+', [status(thm)], ['21', '31'])).
% 0.23/0.52  thf('33', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(dt_m1_pre_topc, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( l1_pre_topc @ A ) =>
% 0.23/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.23/0.52  thf('34', plain,
% 0.23/0.52      (![X21 : $i, X22 : $i]:
% 0.23/0.52         (~ (m1_pre_topc @ X21 @ X22)
% 0.23/0.52          | (l1_pre_topc @ X21)
% 0.23/0.52          | ~ (l1_pre_topc @ X22))),
% 0.23/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.23/0.52  thf('35', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.52  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('37', plain, ((l1_pre_topc @ sk_C_1)),
% 0.23/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.52  thf(dt_l1_pre_topc, axiom,
% 0.23/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.52  thf('38', plain,
% 0.23/0.52      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.23/0.53  thf('39', plain, ((l1_struct_0 @ sk_C_1)),
% 0.23/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.23/0.53  thf('40', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['32', '39'])).
% 0.23/0.53  thf('41', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.23/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.53  thf('42', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k3_xboole_0 @ X0 @ sk_B)
% 0.23/0.53           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.23/0.53      inference('demod', [status(thm)], ['8', '11'])).
% 0.23/0.53  thf('43', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.23/0.53  thf('44', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['32', '39'])).
% 0.23/0.53  thf('45', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.23/0.53          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.23/0.53          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.53          | (v3_pre_topc @ sk_B @ sk_C_1)
% 0.23/0.53          | ~ (l1_pre_topc @ X0))),
% 0.23/0.53      inference('demod', [status(thm)],
% 0.23/0.53                ['15', '20', '40', '41', '42', '43', '44'])).
% 0.23/0.53  thf('46', plain,
% 0.23/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.53        | (v3_pre_topc @ sk_B @ sk_C_1)
% 0.23/0.53        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.23/0.53        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['3', '45'])).
% 0.23/0.53  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('48', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('49', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('50', plain, ((v3_pre_topc @ sk_B @ sk_C_1)),
% 0.23/0.53      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.23/0.53  thf('51', plain, ($false), inference('demod', [status(thm)], ['2', '50'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
