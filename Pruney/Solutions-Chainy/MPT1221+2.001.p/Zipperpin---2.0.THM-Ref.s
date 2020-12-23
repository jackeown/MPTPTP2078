%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8UcP6S1a2W

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:42 EST 2020

% Result     : Theorem 5.36s
% Output     : Refutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :  226 (13849 expanded)
%              Number of leaves         :   41 (4249 expanded)
%              Depth                    :   39
%              Number of atoms          : 1840 (122161 expanded)
%              Number of equality atoms :  133 (8174 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('8',plain,(
    ! [X47: $i] :
      ( ( l1_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('30',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('33',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('40',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','40'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('47',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('52',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X26 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('53',plain,(
    ! [X23: $i] :
      ( ( k2_subset_1 @ X23 )
      = X23 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('58',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('64',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('68',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('71',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('74',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','74'])).

thf('76',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('81',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('85',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','85'])).

thf('87',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('88',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('89',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('91',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('94',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('96',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['89','96'])).

thf('98',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['86','97'])).

thf('99',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('102',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X37 @ X35 )
        = ( k9_subset_1 @ X36 @ X37 @ ( k3_subset_1 @ X36 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('107',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['89','96'])).

thf('108',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('112',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X20 @ X22 @ X21 )
        = ( k9_subset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('115',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k9_subset_1 @ X34 @ X32 @ X33 )
        = ( k3_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('119',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','117','118'])).

thf('120',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('122',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('123',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('126',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('128',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('130',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('131',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','131'])).

thf('133',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','40'])).

thf('134',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('136',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('138',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('140',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('142',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('143',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['119','143'])).

thf('145',plain,
    ( ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['99','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('147',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['148'])).

thf('150',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('151',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v4_pre_topc @ X45 @ X46 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X46 ) @ ( k2_struct_0 @ X46 ) @ X45 ) @ X46 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('152',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['147','155'])).

thf('157',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('158',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('159',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('160',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('161',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['148'])).

thf('162',plain,
    ( ( ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('164',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['159','164'])).

thf('166',plain,
    ( ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['158','165'])).

thf('167',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('168',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('170',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X46 ) @ ( k2_struct_0 @ X46 ) @ X45 ) @ X46 )
      | ( v4_pre_topc @ X45 @ X46 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('171',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['168','174'])).

thf('176',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('177',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['148'])).

thf('179',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['157','177','178'])).

thf('180',plain,(
    v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['156','179'])).

thf('181',plain,
    ( $false
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['1','98','180'])).

thf('182',plain,(
    ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['157','177'])).

thf('183',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['181','182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8UcP6S1a2W
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:08:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 5.36/5.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.36/5.58  % Solved by: fo/fo7.sh
% 5.36/5.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.36/5.58  % done 5879 iterations in 5.122s
% 5.36/5.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.36/5.58  % SZS output start Refutation
% 5.36/5.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.36/5.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.36/5.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 5.36/5.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 5.36/5.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.36/5.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.36/5.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.36/5.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.36/5.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.36/5.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.36/5.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.36/5.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.36/5.58  thf(sk_B_type, type, sk_B: $i).
% 5.36/5.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.36/5.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.36/5.58  thf(sk_A_type, type, sk_A: $i).
% 5.36/5.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.36/5.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 5.36/5.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.36/5.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.36/5.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.36/5.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.36/5.58  thf(t29_tops_1, conjecture,
% 5.36/5.58    (![A:$i]:
% 5.36/5.58     ( ( l1_pre_topc @ A ) =>
% 5.36/5.58       ( ![B:$i]:
% 5.36/5.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.36/5.58           ( ( v4_pre_topc @ B @ A ) <=>
% 5.36/5.58             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 5.36/5.58  thf(zf_stmt_0, negated_conjecture,
% 5.36/5.58    (~( ![A:$i]:
% 5.36/5.58        ( ( l1_pre_topc @ A ) =>
% 5.36/5.58          ( ![B:$i]:
% 5.36/5.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.36/5.58              ( ( v4_pre_topc @ B @ A ) <=>
% 5.36/5.58                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 5.36/5.58    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 5.36/5.58  thf('0', plain,
% 5.36/5.58      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.36/5.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf('1', plain,
% 5.36/5.58      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.36/5.58         <= (~
% 5.36/5.58             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.36/5.58      inference('split', [status(esa)], ['0'])).
% 5.36/5.58  thf(d3_struct_0, axiom,
% 5.36/5.58    (![A:$i]:
% 5.36/5.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.36/5.58  thf('2', plain,
% 5.36/5.58      (![X44 : $i]:
% 5.36/5.58         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 5.36/5.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.36/5.58  thf('3', plain,
% 5.36/5.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf(d5_subset_1, axiom,
% 5.36/5.58    (![A:$i,B:$i]:
% 5.36/5.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.36/5.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.36/5.58  thf('4', plain,
% 5.36/5.58      (![X24 : $i, X25 : $i]:
% 5.36/5.58         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 5.36/5.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 5.36/5.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.36/5.58  thf('5', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup-', [status(thm)], ['3', '4'])).
% 5.36/5.58  thf('6', plain,
% 5.36/5.58      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58        | ~ (l1_struct_0 @ sk_A))),
% 5.36/5.58      inference('sup+', [status(thm)], ['2', '5'])).
% 5.36/5.58  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf(dt_l1_pre_topc, axiom,
% 5.36/5.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.36/5.58  thf('8', plain, (![X47 : $i]: ((l1_struct_0 @ X47) | ~ (l1_pre_topc @ X47))),
% 5.36/5.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.36/5.58  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 5.36/5.58      inference('sup-', [status(thm)], ['7', '8'])).
% 5.36/5.58  thf('10', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['6', '9'])).
% 5.36/5.58  thf('11', plain,
% 5.36/5.58      (![X44 : $i]:
% 5.36/5.58         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 5.36/5.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.36/5.58  thf('12', plain,
% 5.36/5.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf('13', plain,
% 5.36/5.58      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.36/5.58        | ~ (l1_struct_0 @ sk_A))),
% 5.36/5.58      inference('sup+', [status(thm)], ['11', '12'])).
% 5.36/5.58  thf('14', plain, ((l1_struct_0 @ sk_A)),
% 5.36/5.58      inference('sup-', [status(thm)], ['7', '8'])).
% 5.36/5.58  thf('15', plain,
% 5.36/5.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['13', '14'])).
% 5.36/5.58  thf('16', plain,
% 5.36/5.58      (![X24 : $i, X25 : $i]:
% 5.36/5.58         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 5.36/5.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 5.36/5.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.36/5.58  thf('17', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup-', [status(thm)], ['15', '16'])).
% 5.36/5.58  thf('18', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['10', '17'])).
% 5.36/5.58  thf('19', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup-', [status(thm)], ['15', '16'])).
% 5.36/5.58  thf(t48_xboole_1, axiom,
% 5.36/5.58    (![A:$i,B:$i]:
% 5.36/5.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.36/5.58  thf('20', plain,
% 5.36/5.58      (![X16 : $i, X17 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.36/5.58           = (k3_xboole_0 @ X16 @ X17))),
% 5.36/5.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.36/5.58  thf('21', plain,
% 5.36/5.58      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 5.36/5.58         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58         = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['19', '20'])).
% 5.36/5.58  thf(commutativity_k2_tarski, axiom,
% 5.36/5.58    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.36/5.58  thf('22', plain,
% 5.36/5.58      (![X18 : $i, X19 : $i]:
% 5.36/5.58         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 5.36/5.58      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.36/5.58  thf(t12_setfam_1, axiom,
% 5.36/5.58    (![A:$i,B:$i]:
% 5.36/5.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.36/5.58  thf('23', plain,
% 5.36/5.58      (![X39 : $i, X40 : $i]:
% 5.36/5.58         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 5.36/5.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.36/5.58  thf('24', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]:
% 5.36/5.58         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 5.36/5.58      inference('sup+', [status(thm)], ['22', '23'])).
% 5.36/5.58  thf('25', plain,
% 5.36/5.58      (![X39 : $i, X40 : $i]:
% 5.36/5.58         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 5.36/5.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.36/5.58  thf('26', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.36/5.58      inference('sup+', [status(thm)], ['24', '25'])).
% 5.36/5.58  thf('27', plain,
% 5.36/5.58      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 5.36/5.58         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['21', '26'])).
% 5.36/5.58  thf('28', plain,
% 5.36/5.58      (![X44 : $i]:
% 5.36/5.58         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 5.36/5.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.36/5.58  thf('29', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup-', [status(thm)], ['3', '4'])).
% 5.36/5.58  thf('30', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['6', '9'])).
% 5.36/5.58  thf('31', plain,
% 5.36/5.58      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['29', '30'])).
% 5.36/5.58  thf('32', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup-', [status(thm)], ['15', '16'])).
% 5.36/5.58  thf('33', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['31', '32'])).
% 5.36/5.58  thf('34', plain,
% 5.36/5.58      (![X16 : $i, X17 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.36/5.58           = (k3_xboole_0 @ X16 @ X17))),
% 5.36/5.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.36/5.58  thf('35', plain,
% 5.36/5.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['33', '34'])).
% 5.36/5.58  thf('36', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.36/5.58      inference('sup+', [status(thm)], ['24', '25'])).
% 5.36/5.58  thf('37', plain,
% 5.36/5.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['35', '36'])).
% 5.36/5.58  thf('38', plain,
% 5.36/5.58      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 5.36/5.58          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58          = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 5.36/5.58        | ~ (l1_struct_0 @ sk_A))),
% 5.36/5.58      inference('sup+', [status(thm)], ['28', '37'])).
% 5.36/5.58  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 5.36/5.58      inference('sup-', [status(thm)], ['7', '8'])).
% 5.36/5.58  thf('40', plain,
% 5.36/5.58      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 5.36/5.58         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['38', '39'])).
% 5.36/5.58  thf('41', plain,
% 5.36/5.58      (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))
% 5.36/5.58         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['27', '40'])).
% 5.36/5.58  thf(t100_xboole_1, axiom,
% 5.36/5.58    (![A:$i,B:$i]:
% 5.36/5.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.36/5.58  thf('42', plain,
% 5.36/5.58      (![X13 : $i, X14 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X13 @ X14)
% 5.36/5.58           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 5.36/5.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.36/5.58  thf('43', plain,
% 5.36/5.58      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.36/5.58         = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))))),
% 5.36/5.58      inference('sup+', [status(thm)], ['41', '42'])).
% 5.36/5.58  thf('44', plain,
% 5.36/5.58      (![X13 : $i, X14 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X13 @ X14)
% 5.36/5.58           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 5.36/5.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.36/5.58  thf('45', plain,
% 5.36/5.58      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.36/5.58         = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['43', '44'])).
% 5.36/5.58  thf(d5_xboole_0, axiom,
% 5.36/5.58    (![A:$i,B:$i,C:$i]:
% 5.36/5.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 5.36/5.58       ( ![D:$i]:
% 5.36/5.58         ( ( r2_hidden @ D @ C ) <=>
% 5.36/5.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 5.36/5.58  thf('46', plain,
% 5.36/5.58      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.36/5.58         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 5.36/5.58          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 5.36/5.58          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.36/5.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.36/5.58  thf(t4_subset_1, axiom,
% 5.36/5.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.36/5.58  thf('47', plain,
% 5.36/5.58      (![X38 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 5.36/5.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.36/5.58  thf('48', plain,
% 5.36/5.58      (![X24 : $i, X25 : $i]:
% 5.36/5.58         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 5.36/5.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 5.36/5.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.36/5.58  thf('49', plain,
% 5.36/5.58      (![X0 : $i]:
% 5.36/5.58         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 5.36/5.58      inference('sup-', [status(thm)], ['47', '48'])).
% 5.36/5.58  thf(t3_boole, axiom,
% 5.36/5.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.36/5.58  thf('50', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 5.36/5.58      inference('cnf', [status(esa)], [t3_boole])).
% 5.36/5.58  thf('51', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 5.36/5.58      inference('sup+', [status(thm)], ['49', '50'])).
% 5.36/5.58  thf(dt_k2_subset_1, axiom,
% 5.36/5.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.36/5.58  thf('52', plain,
% 5.36/5.58      (![X26 : $i]: (m1_subset_1 @ (k2_subset_1 @ X26) @ (k1_zfmisc_1 @ X26))),
% 5.36/5.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 5.36/5.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.36/5.58  thf('53', plain, (![X23 : $i]: ((k2_subset_1 @ X23) = (X23))),
% 5.36/5.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.36/5.58  thf('54', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 5.36/5.58      inference('demod', [status(thm)], ['52', '53'])).
% 5.36/5.58  thf('55', plain,
% 5.36/5.58      (![X24 : $i, X25 : $i]:
% 5.36/5.58         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 5.36/5.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 5.36/5.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.36/5.58  thf('56', plain,
% 5.36/5.58      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 5.36/5.58      inference('sup-', [status(thm)], ['54', '55'])).
% 5.36/5.58  thf('57', plain,
% 5.36/5.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.36/5.58         (~ (r2_hidden @ X8 @ X7)
% 5.36/5.58          | ~ (r2_hidden @ X8 @ X6)
% 5.36/5.58          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 5.36/5.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.36/5.58  thf('58', plain,
% 5.36/5.58      (![X5 : $i, X6 : $i, X8 : $i]:
% 5.36/5.58         (~ (r2_hidden @ X8 @ X6)
% 5.36/5.58          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 5.36/5.58      inference('simplify', [status(thm)], ['57'])).
% 5.36/5.58  thf('59', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]:
% 5.36/5.58         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))
% 5.36/5.58          | ~ (r2_hidden @ X1 @ X0))),
% 5.36/5.58      inference('sup-', [status(thm)], ['56', '58'])).
% 5.36/5.58  thf('60', plain,
% 5.36/5.58      (![X0 : $i]:
% 5.36/5.58         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 5.36/5.58      inference('sup-', [status(thm)], ['51', '59'])).
% 5.36/5.58  thf('61', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.36/5.58      inference('simplify', [status(thm)], ['60'])).
% 5.36/5.58  thf('62', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]:
% 5.36/5.58         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 5.36/5.58          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.36/5.58      inference('sup-', [status(thm)], ['46', '61'])).
% 5.36/5.58  thf('63', plain,
% 5.36/5.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf(l3_subset_1, axiom,
% 5.36/5.58    (![A:$i,B:$i]:
% 5.36/5.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.36/5.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 5.36/5.58  thf('64', plain,
% 5.36/5.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.36/5.58         (~ (r2_hidden @ X29 @ X30)
% 5.36/5.58          | (r2_hidden @ X29 @ X31)
% 5.36/5.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 5.36/5.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 5.36/5.58  thf('65', plain,
% 5.36/5.58      (![X0 : $i]:
% 5.36/5.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 5.36/5.58      inference('sup-', [status(thm)], ['63', '64'])).
% 5.36/5.58  thf('66', plain,
% 5.36/5.58      (![X0 : $i]:
% 5.36/5.58         (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ X0))
% 5.36/5.58          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_B) @ 
% 5.36/5.58             (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('sup-', [status(thm)], ['62', '65'])).
% 5.36/5.58  thf('67', plain,
% 5.36/5.58      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.36/5.58         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 5.36/5.58          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.36/5.58          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.36/5.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.36/5.58  thf('68', plain,
% 5.36/5.58      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 5.36/5.58        | (r2_hidden @ (sk_D @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.36/5.58           k1_xboole_0)
% 5.36/5.58        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 5.36/5.58      inference('sup-', [status(thm)], ['66', '67'])).
% 5.36/5.58  thf('69', plain,
% 5.36/5.58      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.36/5.58         = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['43', '44'])).
% 5.36/5.58  thf('70', plain,
% 5.36/5.58      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.36/5.58         = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['43', '44'])).
% 5.36/5.58  thf('71', plain,
% 5.36/5.58      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))
% 5.36/5.58        | (r2_hidden @ (sk_D @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.36/5.58           k1_xboole_0)
% 5.36/5.58        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))))),
% 5.36/5.58      inference('demod', [status(thm)], ['68', '69', '70'])).
% 5.36/5.58  thf('72', plain,
% 5.36/5.58      (((r2_hidden @ (sk_D @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.36/5.58         k1_xboole_0)
% 5.36/5.58        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))))),
% 5.36/5.58      inference('simplify', [status(thm)], ['71'])).
% 5.36/5.58  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.36/5.58      inference('simplify', [status(thm)], ['60'])).
% 5.36/5.58  thf('74', plain,
% 5.36/5.58      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('clc', [status(thm)], ['72', '73'])).
% 5.36/5.58  thf('75', plain,
% 5.36/5.58      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 5.36/5.58      inference('demod', [status(thm)], ['45', '74'])).
% 5.36/5.58  thf('76', plain,
% 5.36/5.58      (![X16 : $i, X17 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.36/5.58           = (k3_xboole_0 @ X16 @ X17))),
% 5.36/5.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.36/5.58  thf('77', plain,
% 5.36/5.58      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 5.36/5.58         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['75', '76'])).
% 5.36/5.58  thf('78', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 5.36/5.58      inference('cnf', [status(esa)], [t3_boole])).
% 5.36/5.58  thf('79', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['77', '78'])).
% 5.36/5.58  thf('80', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.36/5.58      inference('sup+', [status(thm)], ['24', '25'])).
% 5.36/5.58  thf('81', plain,
% 5.36/5.58      (![X13 : $i, X14 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X13 @ X14)
% 5.36/5.58           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 5.36/5.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.36/5.58  thf('82', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X0 @ X1)
% 5.36/5.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['80', '81'])).
% 5.36/5.58  thf('83', plain,
% 5.36/5.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['79', '82'])).
% 5.36/5.58  thf('84', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['31', '32'])).
% 5.36/5.58  thf('85', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['83', '84'])).
% 5.36/5.58  thf('86', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['18', '85'])).
% 5.36/5.58  thf('87', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup-', [status(thm)], ['15', '16'])).
% 5.36/5.58  thf('88', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['83', '84'])).
% 5.36/5.58  thf('89', plain,
% 5.36/5.58      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['87', '88'])).
% 5.36/5.58  thf('90', plain,
% 5.36/5.58      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('clc', [status(thm)], ['72', '73'])).
% 5.36/5.58  thf('91', plain,
% 5.36/5.58      (![X16 : $i, X17 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.36/5.58           = (k3_xboole_0 @ X16 @ X17))),
% 5.36/5.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.36/5.58  thf('92', plain,
% 5.36/5.58      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 5.36/5.58         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['90', '91'])).
% 5.36/5.58  thf('93', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 5.36/5.58      inference('cnf', [status(esa)], [t3_boole])).
% 5.36/5.58  thf('94', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['92', '93'])).
% 5.36/5.58  thf('95', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X0 @ X1)
% 5.36/5.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['80', '81'])).
% 5.36/5.58  thf('96', plain,
% 5.36/5.58      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['94', '95'])).
% 5.36/5.58  thf('97', plain,
% 5.36/5.58      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['89', '96'])).
% 5.36/5.58  thf('98', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['86', '97'])).
% 5.36/5.58  thf('99', plain,
% 5.36/5.58      (![X44 : $i]:
% 5.36/5.58         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 5.36/5.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.36/5.58  thf('100', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 5.36/5.58      inference('demod', [status(thm)], ['52', '53'])).
% 5.36/5.58  thf('101', plain,
% 5.36/5.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf(t32_subset_1, axiom,
% 5.36/5.58    (![A:$i,B:$i]:
% 5.36/5.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.36/5.58       ( ![C:$i]:
% 5.36/5.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.36/5.58           ( ( k7_subset_1 @ A @ B @ C ) =
% 5.36/5.58             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 5.36/5.58  thf('102', plain,
% 5.36/5.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 5.36/5.58         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 5.36/5.58          | ((k7_subset_1 @ X36 @ X37 @ X35)
% 5.36/5.58              = (k9_subset_1 @ X36 @ X37 @ (k3_subset_1 @ X36 @ X35)))
% 5.36/5.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 5.36/5.58      inference('cnf', [status(esa)], [t32_subset_1])).
% 5.36/5.58  thf('103', plain,
% 5.36/5.58      (![X0 : $i]:
% 5.36/5.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.36/5.58          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.36/5.58              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 5.36/5.58                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 5.36/5.58      inference('sup-', [status(thm)], ['101', '102'])).
% 5.36/5.58  thf('104', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['10', '17'])).
% 5.36/5.58  thf('105', plain,
% 5.36/5.58      (![X0 : $i]:
% 5.36/5.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.36/5.58          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.36/5.58              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 5.36/5.58                 (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 5.36/5.58      inference('demod', [status(thm)], ['103', '104'])).
% 5.36/5.58  thf('106', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['83', '84'])).
% 5.36/5.58  thf('107', plain,
% 5.36/5.58      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['89', '96'])).
% 5.36/5.58  thf('108', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['106', '107'])).
% 5.36/5.58  thf('109', plain,
% 5.36/5.58      (![X0 : $i]:
% 5.36/5.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.36/5.58          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.36/5.58              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 5.36/5.58                 (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 5.36/5.58      inference('demod', [status(thm)], ['105', '108'])).
% 5.36/5.58  thf('110', plain,
% 5.36/5.58      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('sup-', [status(thm)], ['100', '109'])).
% 5.36/5.58  thf('111', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 5.36/5.58      inference('demod', [status(thm)], ['52', '53'])).
% 5.36/5.58  thf(commutativity_k9_subset_1, axiom,
% 5.36/5.58    (![A:$i,B:$i,C:$i]:
% 5.36/5.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.36/5.58       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 5.36/5.58  thf('112', plain,
% 5.36/5.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.36/5.58         (((k9_subset_1 @ X20 @ X22 @ X21) = (k9_subset_1 @ X20 @ X21 @ X22))
% 5.36/5.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 5.36/5.58      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 5.36/5.58  thf('113', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]:
% 5.36/5.58         ((k9_subset_1 @ X0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 5.36/5.58      inference('sup-', [status(thm)], ['111', '112'])).
% 5.36/5.58  thf('114', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 5.36/5.58      inference('demod', [status(thm)], ['52', '53'])).
% 5.36/5.58  thf(redefinition_k9_subset_1, axiom,
% 5.36/5.58    (![A:$i,B:$i,C:$i]:
% 5.36/5.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.36/5.58       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 5.36/5.58  thf('115', plain,
% 5.36/5.58      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.36/5.58         (((k9_subset_1 @ X34 @ X32 @ X33) = (k3_xboole_0 @ X32 @ X33))
% 5.36/5.58          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 5.36/5.58      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.36/5.58  thf('116', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]:
% 5.36/5.58         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 5.36/5.58      inference('sup-', [status(thm)], ['114', '115'])).
% 5.36/5.58  thf('117', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]:
% 5.36/5.58         ((k3_xboole_0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 5.36/5.58      inference('demod', [status(thm)], ['113', '116'])).
% 5.36/5.58  thf('118', plain,
% 5.36/5.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.36/5.58      inference('sup+', [status(thm)], ['24', '25'])).
% 5.36/5.58  thf('119', plain,
% 5.36/5.58      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('demod', [status(thm)], ['110', '117', '118'])).
% 5.36/5.58  thf('120', plain,
% 5.36/5.58      (![X44 : $i]:
% 5.36/5.58         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 5.36/5.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.36/5.58  thf('121', plain,
% 5.36/5.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf(dt_k3_subset_1, axiom,
% 5.36/5.58    (![A:$i,B:$i]:
% 5.36/5.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.36/5.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.36/5.58  thf('122', plain,
% 5.36/5.58      (![X27 : $i, X28 : $i]:
% 5.36/5.58         ((m1_subset_1 @ (k3_subset_1 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))
% 5.36/5.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 5.36/5.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 5.36/5.58  thf('123', plain,
% 5.36/5.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.36/5.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('sup-', [status(thm)], ['121', '122'])).
% 5.36/5.58  thf('124', plain,
% 5.36/5.58      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.36/5.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.36/5.58        | ~ (l1_struct_0 @ sk_A))),
% 5.36/5.58      inference('sup+', [status(thm)], ['120', '123'])).
% 5.36/5.58  thf('125', plain, ((l1_struct_0 @ sk_A)),
% 5.36/5.58      inference('sup-', [status(thm)], ['7', '8'])).
% 5.36/5.58  thf('126', plain,
% 5.36/5.58      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.36/5.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['124', '125'])).
% 5.36/5.58  thf('127', plain,
% 5.36/5.58      (![X24 : $i, X25 : $i]:
% 5.36/5.58         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 5.36/5.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 5.36/5.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.36/5.58  thf('128', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('sup-', [status(thm)], ['126', '127'])).
% 5.36/5.58  thf('129', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('sup-', [status(thm)], ['126', '127'])).
% 5.36/5.58  thf('130', plain,
% 5.36/5.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['35', '36'])).
% 5.36/5.58  thf('131', plain,
% 5.36/5.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['129', '130'])).
% 5.36/5.58  thf('132', plain,
% 5.36/5.58      (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('demod', [status(thm)], ['128', '131'])).
% 5.36/5.58  thf('133', plain,
% 5.36/5.58      (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))
% 5.36/5.58         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['27', '40'])).
% 5.36/5.58  thf('134', plain,
% 5.36/5.58      (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('demod', [status(thm)], ['132', '133'])).
% 5.36/5.58  thf('135', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['92', '93'])).
% 5.36/5.58  thf('136', plain,
% 5.36/5.58      (((sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('demod', [status(thm)], ['134', '135'])).
% 5.36/5.58  thf('137', plain,
% 5.36/5.58      (![X16 : $i, X17 : $i]:
% 5.36/5.58         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.36/5.58           = (k3_xboole_0 @ X16 @ X17))),
% 5.36/5.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.36/5.58  thf('138', plain,
% 5.36/5.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['136', '137'])).
% 5.36/5.58  thf('139', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['31', '32'])).
% 5.36/5.58  thf('140', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('demod', [status(thm)], ['138', '139'])).
% 5.36/5.58  thf('141', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['106', '107'])).
% 5.36/5.58  thf('142', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['106', '107'])).
% 5.36/5.58  thf('143', plain,
% 5.36/5.58      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.36/5.58            (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.36/5.58      inference('demod', [status(thm)], ['140', '141', '142'])).
% 5.36/5.58  thf('144', plain,
% 5.36/5.58      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['119', '143'])).
% 5.36/5.58  thf('145', plain,
% 5.36/5.58      ((((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.36/5.58        | ~ (l1_struct_0 @ sk_A))),
% 5.36/5.58      inference('sup+', [status(thm)], ['99', '144'])).
% 5.36/5.58  thf('146', plain, ((l1_struct_0 @ sk_A)),
% 5.36/5.58      inference('sup-', [status(thm)], ['7', '8'])).
% 5.36/5.58  thf('147', plain,
% 5.36/5.58      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['145', '146'])).
% 5.36/5.58  thf('148', plain,
% 5.36/5.58      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.36/5.58        | (v4_pre_topc @ sk_B @ sk_A))),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf('149', plain,
% 5.36/5.58      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.36/5.58      inference('split', [status(esa)], ['148'])).
% 5.36/5.58  thf('150', plain,
% 5.36/5.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf(d6_pre_topc, axiom,
% 5.36/5.58    (![A:$i]:
% 5.36/5.58     ( ( l1_pre_topc @ A ) =>
% 5.36/5.58       ( ![B:$i]:
% 5.36/5.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.36/5.58           ( ( v4_pre_topc @ B @ A ) <=>
% 5.36/5.58             ( v3_pre_topc @
% 5.36/5.58               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 5.36/5.58               A ) ) ) ) ))).
% 5.36/5.58  thf('151', plain,
% 5.36/5.58      (![X45 : $i, X46 : $i]:
% 5.36/5.58         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 5.36/5.58          | ~ (v4_pre_topc @ X45 @ X46)
% 5.36/5.58          | (v3_pre_topc @ 
% 5.36/5.58             (k7_subset_1 @ (u1_struct_0 @ X46) @ (k2_struct_0 @ X46) @ X45) @ 
% 5.36/5.58             X46)
% 5.36/5.58          | ~ (l1_pre_topc @ X46))),
% 5.36/5.58      inference('cnf', [status(esa)], [d6_pre_topc])).
% 5.36/5.58  thf('152', plain,
% 5.36/5.58      ((~ (l1_pre_topc @ sk_A)
% 5.36/5.58        | (v3_pre_topc @ 
% 5.36/5.58           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.36/5.58           sk_A)
% 5.36/5.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.36/5.58      inference('sup-', [status(thm)], ['150', '151'])).
% 5.36/5.58  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf('154', plain,
% 5.36/5.58      (((v3_pre_topc @ 
% 5.36/5.58         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.36/5.58         sk_A)
% 5.36/5.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.36/5.58      inference('demod', [status(thm)], ['152', '153'])).
% 5.36/5.58  thf('155', plain,
% 5.36/5.58      (((v3_pre_topc @ 
% 5.36/5.58         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.36/5.58         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.36/5.58      inference('sup-', [status(thm)], ['149', '154'])).
% 5.36/5.58  thf('156', plain,
% 5.36/5.58      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.36/5.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['147', '155'])).
% 5.36/5.58  thf('157', plain,
% 5.36/5.58      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 5.36/5.58       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.36/5.58      inference('split', [status(esa)], ['0'])).
% 5.36/5.58  thf('158', plain,
% 5.36/5.58      (![X44 : $i]:
% 5.36/5.58         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 5.36/5.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.36/5.58  thf('159', plain,
% 5.36/5.58      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('sup+', [status(thm)], ['83', '84'])).
% 5.36/5.58  thf('160', plain,
% 5.36/5.58      (![X44 : $i]:
% 5.36/5.58         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 5.36/5.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.36/5.58  thf('161', plain,
% 5.36/5.58      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.36/5.58         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.36/5.58      inference('split', [status(esa)], ['148'])).
% 5.36/5.58  thf('162', plain,
% 5.36/5.58      ((((v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.36/5.58         | ~ (l1_struct_0 @ sk_A)))
% 5.36/5.58         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['160', '161'])).
% 5.36/5.58  thf('163', plain, ((l1_struct_0 @ sk_A)),
% 5.36/5.58      inference('sup-', [status(thm)], ['7', '8'])).
% 5.36/5.58  thf('164', plain,
% 5.36/5.58      (((v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.36/5.58         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['162', '163'])).
% 5.36/5.58  thf('165', plain,
% 5.36/5.58      (((v3_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.36/5.58         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['159', '164'])).
% 5.36/5.58  thf('166', plain,
% 5.36/5.58      ((((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.36/5.58         | ~ (l1_struct_0 @ sk_A)))
% 5.36/5.58         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.36/5.58      inference('sup+', [status(thm)], ['158', '165'])).
% 5.36/5.58  thf('167', plain, ((l1_struct_0 @ sk_A)),
% 5.36/5.58      inference('sup-', [status(thm)], ['7', '8'])).
% 5.36/5.58  thf('168', plain,
% 5.36/5.58      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.36/5.58         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['166', '167'])).
% 5.36/5.58  thf('169', plain,
% 5.36/5.58      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.36/5.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.36/5.58      inference('demod', [status(thm)], ['145', '146'])).
% 5.36/5.58  thf('170', plain,
% 5.36/5.58      (![X45 : $i, X46 : $i]:
% 5.36/5.58         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 5.36/5.58          | ~ (v3_pre_topc @ 
% 5.36/5.58               (k7_subset_1 @ (u1_struct_0 @ X46) @ (k2_struct_0 @ X46) @ X45) @ 
% 5.36/5.58               X46)
% 5.36/5.58          | (v4_pre_topc @ X45 @ X46)
% 5.36/5.58          | ~ (l1_pre_topc @ X46))),
% 5.36/5.58      inference('cnf', [status(esa)], [d6_pre_topc])).
% 5.36/5.58  thf('171', plain,
% 5.36/5.58      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.36/5.58        | ~ (l1_pre_topc @ sk_A)
% 5.36/5.58        | (v4_pre_topc @ sk_B @ sk_A)
% 5.36/5.58        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.36/5.58      inference('sup-', [status(thm)], ['169', '170'])).
% 5.36/5.58  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf('173', plain,
% 5.36/5.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.36/5.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.58  thf('174', plain,
% 5.36/5.58      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.36/5.58        | (v4_pre_topc @ sk_B @ sk_A))),
% 5.36/5.58      inference('demod', [status(thm)], ['171', '172', '173'])).
% 5.36/5.58  thf('175', plain,
% 5.36/5.58      (((v4_pre_topc @ sk_B @ sk_A))
% 5.36/5.58         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.36/5.58      inference('sup-', [status(thm)], ['168', '174'])).
% 5.36/5.58  thf('176', plain,
% 5.36/5.58      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 5.36/5.58      inference('split', [status(esa)], ['0'])).
% 5.36/5.58  thf('177', plain,
% 5.36/5.58      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 5.36/5.58       ~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 5.36/5.58      inference('sup-', [status(thm)], ['175', '176'])).
% 5.36/5.58  thf('178', plain,
% 5.36/5.58      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 5.36/5.58       ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 5.36/5.58      inference('split', [status(esa)], ['148'])).
% 5.36/5.58  thf('179', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 5.36/5.58      inference('sat_resolution*', [status(thm)], ['157', '177', '178'])).
% 5.36/5.58  thf('180', plain,
% 5.36/5.58      ((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 5.36/5.58      inference('simpl_trail', [status(thm)], ['156', '179'])).
% 5.36/5.58  thf('181', plain,
% 5.36/5.58      (($false)
% 5.36/5.58         <= (~
% 5.36/5.58             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.36/5.58      inference('demod', [status(thm)], ['1', '98', '180'])).
% 5.36/5.58  thf('182', plain,
% 5.36/5.58      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 5.36/5.58      inference('sat_resolution*', [status(thm)], ['157', '177'])).
% 5.36/5.58  thf('183', plain, ($false),
% 5.36/5.58      inference('simpl_trail', [status(thm)], ['181', '182'])).
% 5.36/5.58  
% 5.36/5.58  % SZS output end Refutation
% 5.36/5.58  
% 5.36/5.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
