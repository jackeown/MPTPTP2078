%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bl2VX5koVT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:18 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 128 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  634 (1327 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k9_subset_1 @ X43 @ X41 @ X42 )
        = ( k3_xboole_0 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k9_subset_1 @ X43 @ X41 @ X42 )
        = ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C_1 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v1_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k9_subset_1 @ X32 @ X34 @ X33 )
        = ( k9_subset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k9_subset_1 @ X43 @ X41 @ X42 )
        = ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C_1 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('15',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_C_1 @ sk_B ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_C_1 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','15'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X37 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

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

thf('26',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) )
      | ( v1_tops_2 @ X48 @ X49 )
      | ~ ( r1_tarski @ X48 @ X50 )
      | ~ ( v1_tops_2 @ X50 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ sk_B ) ) @ X1 )
      | ( v1_tops_2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ sk_B ) ) @ X1 )
      | ( v1_tops_2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ sk_B ) ) @ sk_A )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ sk_B ) ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X36 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('33',plain,(
    ! [X35: $i] :
      ( ( k2_subset_1 @ X35 )
      = X35 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X37 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( r1_tarski @ X30 @ X28 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('42',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ X30 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('45',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k9_subset_1 @ X43 @ X41 @ X42 )
        = ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['31','47'])).

thf('49',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) @ sk_A ) ),
    inference('sup+',[status(thm)],['17','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['16','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bl2VX5koVT
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.77  % Solved by: fo/fo7.sh
% 0.53/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.77  % done 514 iterations in 0.314s
% 0.53/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.77  % SZS output start Refutation
% 0.53/0.77  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.53/0.77  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.53/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.77  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.53/0.77  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.53/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.77  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.53/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.53/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.77  thf(t21_tops_2, conjecture,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( l1_pre_topc @ A ) =>
% 0.53/0.77       ( ![B:$i]:
% 0.53/0.77         ( ( m1_subset_1 @
% 0.53/0.77             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.77           ( ![C:$i]:
% 0.53/0.77             ( ( m1_subset_1 @
% 0.53/0.77                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.77               ( ( v1_tops_2 @ B @ A ) =>
% 0.53/0.77                 ( v1_tops_2 @
% 0.53/0.77                   ( k9_subset_1 @
% 0.53/0.77                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.53/0.77                   A ) ) ) ) ) ) ))).
% 0.53/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.77    (~( ![A:$i]:
% 0.53/0.77        ( ( l1_pre_topc @ A ) =>
% 0.53/0.77          ( ![B:$i]:
% 0.53/0.77            ( ( m1_subset_1 @
% 0.53/0.77                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.77              ( ![C:$i]:
% 0.53/0.77                ( ( m1_subset_1 @
% 0.53/0.77                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.77                  ( ( v1_tops_2 @ B @ A ) =>
% 0.53/0.77                    ( v1_tops_2 @
% 0.53/0.77                      ( k9_subset_1 @
% 0.53/0.77                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.53/0.77                      A ) ) ) ) ) ) ) )),
% 0.53/0.77    inference('cnf.neg', [status(esa)], [t21_tops_2])).
% 0.53/0.77  thf('0', plain,
% 0.53/0.77      (~ (v1_tops_2 @ 
% 0.53/0.77          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.53/0.77          sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('1', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.53/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(redefinition_k9_subset_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.77       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.53/0.77  thf('2', plain,
% 0.53/0.77      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.53/0.77         (((k9_subset_1 @ X43 @ X41 @ X42) = (k3_xboole_0 @ X41 @ X42))
% 0.53/0.77          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.53/0.77  thf(t12_setfam_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.77  thf('3', plain,
% 0.53/0.77      (![X44 : $i, X45 : $i]:
% 0.53/0.77         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.53/0.77      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.77  thf('4', plain,
% 0.53/0.77      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.53/0.77         (((k9_subset_1 @ X43 @ X41 @ X42)
% 0.53/0.77            = (k1_setfam_1 @ (k2_tarski @ X41 @ X42)))
% 0.53/0.77          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 0.53/0.77      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.77  thf('5', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C_1)
% 0.53/0.77           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C_1)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['1', '4'])).
% 0.53/0.77  thf('6', plain,
% 0.53/0.77      (~ (v1_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C_1)) @ sk_A)),
% 0.53/0.77      inference('demod', [status(thm)], ['0', '5'])).
% 0.53/0.77  thf('7', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_B @ 
% 0.53/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(commutativity_k9_subset_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.77       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.53/0.77  thf('8', plain,
% 0.53/0.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.53/0.77         (((k9_subset_1 @ X32 @ X34 @ X33) = (k9_subset_1 @ X32 @ X33 @ X34))
% 0.53/0.77          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.53/0.77      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.53/0.77  thf('9', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.53/0.77           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.77  thf('10', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_B @ 
% 0.53/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('11', plain,
% 0.53/0.77      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.53/0.77         (((k9_subset_1 @ X43 @ X41 @ X42)
% 0.53/0.77            = (k1_setfam_1 @ (k2_tarski @ X41 @ X42)))
% 0.53/0.77          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 0.53/0.77      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.77  thf('12', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.53/0.77           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.53/0.77  thf('13', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((k1_setfam_1 @ (k2_tarski @ X0 @ sk_B))
% 0.53/0.77           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))),
% 0.53/0.77      inference('demod', [status(thm)], ['9', '12'])).
% 0.53/0.77  thf('14', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C_1)
% 0.53/0.77           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C_1)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['1', '4'])).
% 0.53/0.77  thf('15', plain,
% 0.53/0.77      (((k1_setfam_1 @ (k2_tarski @ sk_C_1 @ sk_B))
% 0.53/0.77         = (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C_1)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['13', '14'])).
% 0.53/0.77  thf('16', plain,
% 0.53/0.77      (~ (v1_tops_2 @ (k1_setfam_1 @ (k2_tarski @ sk_C_1 @ sk_B)) @ sk_A)),
% 0.53/0.77      inference('demod', [status(thm)], ['6', '15'])).
% 0.53/0.77  thf(t70_enumset1, axiom,
% 0.53/0.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.53/0.77  thf('17', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.77  thf('18', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_B @ 
% 0.53/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('19', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.77  thf('20', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_B @ 
% 0.53/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(dt_k9_subset_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.77       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.53/0.77  thf('21', plain,
% 0.53/0.77      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.53/0.77         ((m1_subset_1 @ (k9_subset_1 @ X37 @ X38 @ X39) @ (k1_zfmisc_1 @ X37))
% 0.53/0.77          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X37)))),
% 0.53/0.77      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.53/0.77  thf('22', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (m1_subset_1 @ 
% 0.53/0.77          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 0.53/0.77          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.53/0.77  thf('23', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 0.53/0.77           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.53/0.77  thf('24', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)) @ 
% 0.53/0.77          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('demod', [status(thm)], ['22', '23'])).
% 0.53/0.77  thf('25', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (m1_subset_1 @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ sk_B)) @ 
% 0.53/0.77          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('sup+', [status(thm)], ['19', '24'])).
% 0.53/0.77  thf(t18_tops_2, axiom,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( l1_pre_topc @ A ) =>
% 0.53/0.77       ( ![B:$i]:
% 0.53/0.77         ( ( m1_subset_1 @
% 0.53/0.77             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.77           ( ![C:$i]:
% 0.53/0.77             ( ( m1_subset_1 @
% 0.53/0.77                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.77               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.53/0.77                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.53/0.77  thf('26', plain,
% 0.53/0.77      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.53/0.77         (~ (m1_subset_1 @ X48 @ 
% 0.53/0.77             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))
% 0.53/0.77          | (v1_tops_2 @ X48 @ X49)
% 0.53/0.77          | ~ (r1_tarski @ X48 @ X50)
% 0.53/0.77          | ~ (v1_tops_2 @ X50 @ X49)
% 0.53/0.77          | ~ (m1_subset_1 @ X50 @ 
% 0.53/0.77               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))
% 0.53/0.77          | ~ (l1_pre_topc @ X49))),
% 0.53/0.77      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.53/0.77  thf('27', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (l1_pre_topc @ sk_A)
% 0.53/0.77          | ~ (m1_subset_1 @ X1 @ 
% 0.53/0.77               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.53/0.77          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.53/0.77          | ~ (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ sk_B)) @ X1)
% 0.53/0.77          | (v1_tops_2 @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ sk_B)) @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.77  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('29', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (m1_subset_1 @ X1 @ 
% 0.53/0.77             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.53/0.77          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.53/0.77          | ~ (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ sk_B)) @ X1)
% 0.53/0.77          | (v1_tops_2 @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ sk_B)) @ sk_A))),
% 0.53/0.77      inference('demod', [status(thm)], ['27', '28'])).
% 0.53/0.77  thf('30', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v1_tops_2 @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ sk_B)) @ sk_A)
% 0.53/0.77          | ~ (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ sk_B)) @ 
% 0.53/0.77               sk_B)
% 0.53/0.77          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['18', '29'])).
% 0.53/0.77  thf('31', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.77  thf(dt_k2_subset_1, axiom,
% 0.53/0.77    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.53/0.77  thf('32', plain,
% 0.53/0.77      (![X36 : $i]: (m1_subset_1 @ (k2_subset_1 @ X36) @ (k1_zfmisc_1 @ X36))),
% 0.53/0.77      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.53/0.77  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.53/0.77  thf('33', plain, (![X35 : $i]: ((k2_subset_1 @ X35) = (X35))),
% 0.53/0.77      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.53/0.77  thf('34', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.53/0.77      inference('demod', [status(thm)], ['32', '33'])).
% 0.53/0.77  thf('35', plain,
% 0.53/0.77      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.53/0.77         ((m1_subset_1 @ (k9_subset_1 @ X37 @ X38 @ X39) @ (k1_zfmisc_1 @ X37))
% 0.53/0.77          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X37)))),
% 0.53/0.77      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.53/0.77  thf('36', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.77  thf(t2_subset, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ A @ B ) =>
% 0.53/0.77       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.53/0.77  thf('37', plain,
% 0.53/0.77      (![X46 : $i, X47 : $i]:
% 0.53/0.77         ((r2_hidden @ X46 @ X47)
% 0.53/0.77          | (v1_xboole_0 @ X47)
% 0.53/0.77          | ~ (m1_subset_1 @ X46 @ X47))),
% 0.53/0.77      inference('cnf', [status(esa)], [t2_subset])).
% 0.53/0.77  thf('38', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.53/0.77          | (r2_hidden @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.77  thf(fc1_subset_1, axiom,
% 0.53/0.77    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.53/0.77  thf('39', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.53/0.77      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.53/0.77  thf('40', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (r2_hidden @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.53/0.77      inference('clc', [status(thm)], ['38', '39'])).
% 0.53/0.77  thf(d1_zfmisc_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.53/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.53/0.77  thf('41', plain,
% 0.53/0.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X30 @ X29)
% 0.53/0.77          | (r1_tarski @ X30 @ X28)
% 0.53/0.77          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.53/0.77  thf('42', plain,
% 0.53/0.77      (![X28 : $i, X30 : $i]:
% 0.53/0.77         ((r1_tarski @ X30 @ X28) | ~ (r2_hidden @ X30 @ (k1_zfmisc_1 @ X28)))),
% 0.53/0.77      inference('simplify', [status(thm)], ['41'])).
% 0.53/0.77  thf('43', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.53/0.77      inference('sup-', [status(thm)], ['40', '42'])).
% 0.53/0.77  thf('44', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.53/0.77      inference('demod', [status(thm)], ['32', '33'])).
% 0.53/0.77  thf('45', plain,
% 0.53/0.77      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.53/0.77         (((k9_subset_1 @ X43 @ X41 @ X42)
% 0.53/0.77            = (k1_setfam_1 @ (k2_tarski @ X41 @ X42)))
% 0.53/0.77          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 0.53/0.77      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.77  thf('46', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['44', '45'])).
% 0.53/0.77  thf('47', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.53/0.77      inference('demod', [status(thm)], ['43', '46'])).
% 0.53/0.77  thf('48', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)) @ X0)),
% 0.53/0.77      inference('sup+', [status(thm)], ['31', '47'])).
% 0.53/0.77  thf('49', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('50', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (v1_tops_2 @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ sk_B)) @ sk_A)),
% 0.53/0.77      inference('demod', [status(thm)], ['30', '48', '49'])).
% 0.53/0.77  thf('51', plain,
% 0.53/0.77      (![X0 : $i]: (v1_tops_2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)) @ sk_A)),
% 0.53/0.77      inference('sup+', [status(thm)], ['17', '50'])).
% 0.53/0.77  thf('52', plain, ($false), inference('demod', [status(thm)], ['16', '51'])).
% 0.53/0.77  
% 0.53/0.77  % SZS output end Refutation
% 0.53/0.77  
% 0.61/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
