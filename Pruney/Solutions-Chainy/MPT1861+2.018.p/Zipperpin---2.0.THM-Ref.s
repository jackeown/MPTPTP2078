%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k38x13aMiI

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 164 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  632 (1885 expanded)
%              Number of equality atoms :   17 (  37 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t29_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_tex_2 @ B @ A )
                  | ( v2_tex_2 @ C @ A ) )
               => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v2_tex_2 @ B @ A )
                    | ( v2_tex_2 @ C @ A ) )
                 => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ( v2_tex_2 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ( v2_tex_2 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
        | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','50'])).

thf('52',plain,
    ( ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['25','51'])).

thf('53',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('54',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('56',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['16','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('61',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['4','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k38x13aMiI
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:21 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 211 iterations in 0.085s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(t29_tex_2, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.22/0.54                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( l1_pre_topc @ A ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54              ( ![C:$i]:
% 0.22/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.22/0.54                    ( v2_tex_2 @
% 0.22/0.54                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k9_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.54         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.22/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.54           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('4', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_k9_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.22/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.22/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.54           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.22/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t28_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.22/0.54                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.54          | ~ (v2_tex_2 @ X17 @ X18)
% 0.22/0.54          | ~ (r1_tarski @ X19 @ X17)
% 0.22/0.54          | (v2_tex_2 @ X19 @ X18)
% 0.22/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.54          | ~ (l1_pre_topc @ X18))),
% 0.22/0.54      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_C)
% 0.22/0.54          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_C)
% 0.22/0.54          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('15', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(commutativity_k9_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.54         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 0.22/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.54      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.54           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k3_xboole_0 @ X0 @ sk_C)
% 0.22/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.54         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.22/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.54           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.54      inference('sup+', [status(thm)], ['21', '24'])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.22/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.22/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.54           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.22/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['15'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.54          | ~ (v2_tex_2 @ X17 @ X18)
% 0.22/0.54          | ~ (r1_tarski @ X19 @ X17)
% 0.22/0.54          | (v2_tex_2 @ X19 @ X18)
% 0.22/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.54          | ~ (l1_pre_topc @ X18))),
% 0.22/0.54      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.54          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.54          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.54           | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.22/0.54         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['31', '36'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          ((v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.22/0.54           | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)))
% 0.22/0.54         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['30', '37'])).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.54      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X14 : $i, X16 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('42', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.22/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      (![X14 : $i, X15 : $i]:
% 0.22/0.54         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.22/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.54  thf('47', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.54         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.22/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.22/0.54      inference('demod', [status(thm)], ['46', '49'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A))
% 0.22/0.54         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['38', '50'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (((v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 0.22/0.54         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['25', '51'])).
% 0.22/0.54  thf('53', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.54  thf('54', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.54  thf('55', plain, (((v2_tex_2 @ sk_C @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('split', [status(esa)], ['15'])).
% 0.22/0.54  thf('56', plain, (((v2_tex_2 @ sk_C @ sk_A))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.22/0.54  thf('57', plain, ((v2_tex_2 @ sk_C @ sk_A)),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['16', '56'])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.22/0.54      inference('demod', [status(thm)], ['14', '57'])).
% 0.22/0.54  thf('59', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.22/0.54          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['9', '58'])).
% 0.22/0.54  thf('60', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.22/0.54      inference('demod', [status(thm)], ['46', '49'])).
% 0.22/0.54  thf('61', plain, (![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.22/0.54  thf('62', plain, ($false), inference('demod', [status(thm)], ['4', '61'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
