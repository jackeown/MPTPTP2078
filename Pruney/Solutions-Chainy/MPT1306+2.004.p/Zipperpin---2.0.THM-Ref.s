%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rArWFA9m2E

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:24 EST 2020

% Result     : Theorem 2.87s
% Output     : Refutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 131 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  940 (1962 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X20 @ ( k4_subset_1 @ X20 @ X21 @ X19 ) ) @ ( k3_subset_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k3_subset_1 @ X17 @ ( k7_subset_1 @ X17 @ X18 @ X16 ) )
        = ( k4_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X18 ) @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) )
        = ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) )
    = ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X15 @ X13 )
        = ( k9_subset_1 @ X14 @ X15 @ ( k3_subset_1 @ X14 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) )
        = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) )
        = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) )
    = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('29',plain,
    ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) )
    = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_B ) )
    = ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) ) )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ X0 ) ) )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['13','30','39','40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v2_tops_2 @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ~ ( v2_tops_2 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t19_tops_2])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ X1 )
      | ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ X1 )
      | ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_B ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['4','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rArWFA9m2E
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 2.87/3.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.87/3.05  % Solved by: fo/fo7.sh
% 2.87/3.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.87/3.05  % done 2331 iterations in 2.598s
% 2.87/3.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.87/3.05  % SZS output start Refutation
% 2.87/3.05  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.87/3.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.87/3.05  thf(sk_B_type, type, sk_B: $i).
% 2.87/3.05  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.87/3.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.87/3.05  thf(sk_C_type, type, sk_C: $i).
% 2.87/3.05  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 2.87/3.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.87/3.05  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.87/3.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.87/3.05  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.87/3.05  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.87/3.05  thf(sk_A_type, type, sk_A: $i).
% 2.87/3.05  thf(t24_tops_2, conjecture,
% 2.87/3.05    (![A:$i]:
% 2.87/3.05     ( ( l1_pre_topc @ A ) =>
% 2.87/3.05       ( ![B:$i]:
% 2.87/3.05         ( ( m1_subset_1 @
% 2.87/3.05             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.87/3.05           ( ![C:$i]:
% 2.87/3.05             ( ( m1_subset_1 @
% 2.87/3.05                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.87/3.05               ( ( v2_tops_2 @ B @ A ) =>
% 2.87/3.05                 ( v2_tops_2 @
% 2.87/3.05                   ( k9_subset_1 @
% 2.87/3.05                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 2.87/3.05                   A ) ) ) ) ) ) ))).
% 2.87/3.05  thf(zf_stmt_0, negated_conjecture,
% 2.87/3.05    (~( ![A:$i]:
% 2.87/3.05        ( ( l1_pre_topc @ A ) =>
% 2.87/3.05          ( ![B:$i]:
% 2.87/3.05            ( ( m1_subset_1 @
% 2.87/3.05                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.87/3.05              ( ![C:$i]:
% 2.87/3.05                ( ( m1_subset_1 @
% 2.87/3.05                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.87/3.05                  ( ( v2_tops_2 @ B @ A ) =>
% 2.87/3.05                    ( v2_tops_2 @
% 2.87/3.05                      ( k9_subset_1 @
% 2.87/3.05                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 2.87/3.05                      A ) ) ) ) ) ) ) )),
% 2.87/3.05    inference('cnf.neg', [status(esa)], [t24_tops_2])).
% 2.87/3.05  thf('0', plain,
% 2.87/3.05      (~ (v2_tops_2 @ 
% 2.87/3.05          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 2.87/3.05          sk_A)),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('1', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_B @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf(commutativity_k9_subset_1, axiom,
% 2.87/3.05    (![A:$i,B:$i,C:$i]:
% 2.87/3.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 2.87/3.05  thf('2', plain,
% 2.87/3.05      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.87/3.05         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 2.87/3.05          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 2.87/3.05      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 2.87/3.05  thf('3', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 2.87/3.05           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))),
% 2.87/3.05      inference('sup-', [status(thm)], ['1', '2'])).
% 2.87/3.05  thf('4', plain,
% 2.87/3.05      (~ (v2_tops_2 @ 
% 2.87/3.05          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ sk_B) @ 
% 2.87/3.05          sk_A)),
% 2.87/3.05      inference('demod', [status(thm)], ['0', '3'])).
% 2.87/3.05  thf('5', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_B @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf(dt_k3_subset_1, axiom,
% 2.87/3.05    (![A:$i,B:$i]:
% 2.87/3.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.87/3.05  thf('6', plain,
% 2.87/3.05      (![X6 : $i, X7 : $i]:
% 2.87/3.05         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 2.87/3.05          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 2.87/3.05      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.87/3.05  thf('7', plain,
% 2.87/3.05      ((m1_subset_1 @ 
% 2.87/3.05        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('sup-', [status(thm)], ['5', '6'])).
% 2.87/3.05  thf('8', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_C @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('9', plain,
% 2.87/3.05      (![X6 : $i, X7 : $i]:
% 2.87/3.05         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 2.87/3.05          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 2.87/3.05      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.87/3.05  thf('10', plain,
% 2.87/3.05      ((m1_subset_1 @ 
% 2.87/3.05        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C) @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('sup-', [status(thm)], ['8', '9'])).
% 2.87/3.05  thf(t41_subset_1, axiom,
% 2.87/3.05    (![A:$i,B:$i]:
% 2.87/3.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05       ( ![C:$i]:
% 2.87/3.05         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05           ( r1_tarski @
% 2.87/3.05             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 2.87/3.05             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 2.87/3.05  thf('11', plain,
% 2.87/3.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.87/3.05         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 2.87/3.05          | (r1_tarski @ 
% 2.87/3.05             (k3_subset_1 @ X20 @ (k4_subset_1 @ X20 @ X21 @ X19)) @ 
% 2.87/3.05             (k3_subset_1 @ X20 @ X21))
% 2.87/3.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 2.87/3.05      inference('cnf', [status(esa)], [t41_subset_1])).
% 2.87/3.05  thf('12', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         (~ (m1_subset_1 @ X0 @ 
% 2.87/3.05             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.87/3.05          | (r1_tarski @ 
% 2.87/3.05             (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05              (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ 
% 2.87/3.05               (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))) @ 
% 2.87/3.05             (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0)))),
% 2.87/3.05      inference('sup-', [status(thm)], ['10', '11'])).
% 2.87/3.05  thf('13', plain,
% 2.87/3.05      ((r1_tarski @ 
% 2.87/3.05        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05         (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05          (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 2.87/3.05          (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))) @ 
% 2.87/3.05        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05         (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B)))),
% 2.87/3.05      inference('sup-', [status(thm)], ['7', '12'])).
% 2.87/3.05  thf('14', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_B @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('15', plain,
% 2.87/3.05      ((m1_subset_1 @ 
% 2.87/3.05        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C) @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('sup-', [status(thm)], ['8', '9'])).
% 2.87/3.05  thf(t33_subset_1, axiom,
% 2.87/3.05    (![A:$i,B:$i]:
% 2.87/3.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05       ( ![C:$i]:
% 2.87/3.05         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 2.87/3.05             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 2.87/3.05  thf('16', plain,
% 2.87/3.05      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.87/3.05         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.87/3.05          | ((k3_subset_1 @ X17 @ (k7_subset_1 @ X17 @ X18 @ X16))
% 2.87/3.05              = (k4_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X18) @ X16))
% 2.87/3.05          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 2.87/3.05      inference('cnf', [status(esa)], [t33_subset_1])).
% 2.87/3.05  thf('17', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         (~ (m1_subset_1 @ X0 @ 
% 2.87/3.05             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.87/3.05          | ((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05              (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ 
% 2.87/3.05               (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))
% 2.87/3.05              = (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05                 (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0) @ 
% 2.87/3.05                 (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))))),
% 2.87/3.05      inference('sup-', [status(thm)], ['15', '16'])).
% 2.87/3.05  thf('18', plain,
% 2.87/3.05      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05         (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 2.87/3.05          (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))
% 2.87/3.05         = (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05            (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 2.87/3.05            (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))),
% 2.87/3.05      inference('sup-', [status(thm)], ['14', '17'])).
% 2.87/3.05  thf('19', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_B @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('20', plain,
% 2.87/3.05      ((m1_subset_1 @ 
% 2.87/3.05        (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C) @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('sup-', [status(thm)], ['8', '9'])).
% 2.87/3.05  thf(t32_subset_1, axiom,
% 2.87/3.05    (![A:$i,B:$i]:
% 2.87/3.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05       ( ![C:$i]:
% 2.87/3.05         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05           ( ( k7_subset_1 @ A @ B @ C ) =
% 2.87/3.05             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 2.87/3.05  thf('21', plain,
% 2.87/3.05      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.87/3.05         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 2.87/3.05          | ((k7_subset_1 @ X14 @ X15 @ X13)
% 2.87/3.05              = (k9_subset_1 @ X14 @ X15 @ (k3_subset_1 @ X14 @ X13)))
% 2.87/3.05          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 2.87/3.05      inference('cnf', [status(esa)], [t32_subset_1])).
% 2.87/3.05  thf('22', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         (~ (m1_subset_1 @ X0 @ 
% 2.87/3.05             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.87/3.05          | ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ 
% 2.87/3.05              (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))
% 2.87/3.05              = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ 
% 2.87/3.05                 (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05                  (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))))),
% 2.87/3.05      inference('sup-', [status(thm)], ['20', '21'])).
% 2.87/3.05  thf('23', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_C @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf(involutiveness_k3_subset_1, axiom,
% 2.87/3.05    (![A:$i,B:$i]:
% 2.87/3.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.87/3.05  thf('24', plain,
% 2.87/3.05      (![X11 : $i, X12 : $i]:
% 2.87/3.05         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 2.87/3.05          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 2.87/3.05      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.87/3.05  thf('25', plain,
% 2.87/3.05      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05         (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)) = (
% 2.87/3.05         sk_C))),
% 2.87/3.05      inference('sup-', [status(thm)], ['23', '24'])).
% 2.87/3.05  thf('26', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         (~ (m1_subset_1 @ X0 @ 
% 2.87/3.05             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.87/3.05          | ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ 
% 2.87/3.05              (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))
% 2.87/3.05              = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)))),
% 2.87/3.05      inference('demod', [status(thm)], ['22', '25'])).
% 2.87/3.05  thf('27', plain,
% 2.87/3.05      (((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 2.87/3.05         (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))
% 2.87/3.05         = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C))),
% 2.87/3.05      inference('sup-', [status(thm)], ['19', '26'])).
% 2.87/3.05  thf('28', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 2.87/3.05           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))),
% 2.87/3.05      inference('sup-', [status(thm)], ['1', '2'])).
% 2.87/3.05  thf('29', plain,
% 2.87/3.05      (((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 2.87/3.05         (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C))
% 2.87/3.05         = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ sk_B))),
% 2.87/3.05      inference('demod', [status(thm)], ['27', '28'])).
% 2.87/3.05  thf('30', plain,
% 2.87/3.05      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05         (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ sk_B))
% 2.87/3.05         = (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05            (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 2.87/3.05            (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C)))),
% 2.87/3.05      inference('demod', [status(thm)], ['18', '29'])).
% 2.87/3.05  thf('31', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_C @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('32', plain,
% 2.87/3.05      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.87/3.05         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 2.87/3.05          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 2.87/3.05      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 2.87/3.05  thf('33', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 2.87/3.05           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ X0))),
% 2.87/3.05      inference('sup-', [status(thm)], ['31', '32'])).
% 2.87/3.05  thf('34', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_C @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf(dt_k9_subset_1, axiom,
% 2.87/3.05    (![A:$i,B:$i,C:$i]:
% 2.87/3.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.87/3.05       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.87/3.05  thf('35', plain,
% 2.87/3.05      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.87/3.05         ((m1_subset_1 @ (k9_subset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 2.87/3.05          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X8)))),
% 2.87/3.05      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 2.87/3.05  thf('36', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         (m1_subset_1 @ 
% 2.87/3.05          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C) @ 
% 2.87/3.05          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('sup-', [status(thm)], ['34', '35'])).
% 2.87/3.05  thf('37', plain,
% 2.87/3.05      (![X11 : $i, X12 : $i]:
% 2.87/3.05         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 2.87/3.05          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 2.87/3.05      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.87/3.05  thf('38', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         ((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05           (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05            (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)))
% 2.87/3.05           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C))),
% 2.87/3.05      inference('sup-', [status(thm)], ['36', '37'])).
% 2.87/3.05  thf('39', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         ((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05           (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05            (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ X0)))
% 2.87/3.05           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C))),
% 2.87/3.05      inference('sup+', [status(thm)], ['33', '38'])).
% 2.87/3.05  thf('40', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B)
% 2.87/3.05           = (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0))),
% 2.87/3.05      inference('sup-', [status(thm)], ['1', '2'])).
% 2.87/3.05  thf('41', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_B @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('42', plain,
% 2.87/3.05      (![X11 : $i, X12 : $i]:
% 2.87/3.05         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 2.87/3.05          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 2.87/3.05      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.87/3.05  thf('43', plain,
% 2.87/3.05      (((k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 2.87/3.05         (k3_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B)) = (
% 2.87/3.05         sk_B))),
% 2.87/3.05      inference('sup-', [status(thm)], ['41', '42'])).
% 2.87/3.05  thf('44', plain,
% 2.87/3.05      ((r1_tarski @ 
% 2.87/3.05        (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ sk_B) @ 
% 2.87/3.05        sk_B)),
% 2.87/3.05      inference('demod', [status(thm)], ['13', '30', '39', '40', '43'])).
% 2.87/3.05  thf('45', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_B @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('46', plain,
% 2.87/3.05      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.87/3.05         ((m1_subset_1 @ (k9_subset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 2.87/3.05          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X8)))),
% 2.87/3.05      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 2.87/3.05  thf('47', plain,
% 2.87/3.05      (![X0 : $i]:
% 2.87/3.05         (m1_subset_1 @ 
% 2.87/3.05          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 2.87/3.05          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('sup-', [status(thm)], ['45', '46'])).
% 2.87/3.05  thf(t19_tops_2, axiom,
% 2.87/3.05    (![A:$i]:
% 2.87/3.05     ( ( l1_pre_topc @ A ) =>
% 2.87/3.05       ( ![B:$i]:
% 2.87/3.05         ( ( m1_subset_1 @
% 2.87/3.05             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.87/3.05           ( ![C:$i]:
% 2.87/3.05             ( ( m1_subset_1 @
% 2.87/3.05                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.87/3.05               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 2.87/3.05                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 2.87/3.05  thf('48', plain,
% 2.87/3.05      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.87/3.05         (~ (m1_subset_1 @ X22 @ 
% 2.87/3.05             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 2.87/3.05          | (v2_tops_2 @ X22 @ X23)
% 2.87/3.05          | ~ (r1_tarski @ X22 @ X24)
% 2.87/3.05          | ~ (v2_tops_2 @ X24 @ X23)
% 2.87/3.05          | ~ (m1_subset_1 @ X24 @ 
% 2.87/3.05               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 2.87/3.05          | ~ (l1_pre_topc @ X23))),
% 2.87/3.05      inference('cnf', [status(esa)], [t19_tops_2])).
% 2.87/3.05  thf('49', plain,
% 2.87/3.05      (![X0 : $i, X1 : $i]:
% 2.87/3.05         (~ (l1_pre_topc @ sk_A)
% 2.87/3.05          | ~ (m1_subset_1 @ X1 @ 
% 2.87/3.05               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.87/3.05          | ~ (v2_tops_2 @ X1 @ sk_A)
% 2.87/3.05          | ~ (r1_tarski @ 
% 2.87/3.05               (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 2.87/3.05               X1)
% 2.87/3.05          | (v2_tops_2 @ 
% 2.87/3.05             (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 2.87/3.05             sk_A))),
% 2.87/3.05      inference('sup-', [status(thm)], ['47', '48'])).
% 2.87/3.05  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('51', plain,
% 2.87/3.05      (![X0 : $i, X1 : $i]:
% 2.87/3.05         (~ (m1_subset_1 @ X1 @ 
% 2.87/3.05             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.87/3.05          | ~ (v2_tops_2 @ X1 @ sk_A)
% 2.87/3.05          | ~ (r1_tarski @ 
% 2.87/3.05               (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 2.87/3.05               X1)
% 2.87/3.05          | (v2_tops_2 @ 
% 2.87/3.05             (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_B) @ 
% 2.87/3.05             sk_A))),
% 2.87/3.05      inference('demod', [status(thm)], ['49', '50'])).
% 2.87/3.05  thf('52', plain,
% 2.87/3.05      (((v2_tops_2 @ 
% 2.87/3.05         (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ sk_B) @ 
% 2.87/3.05         sk_A)
% 2.87/3.05        | ~ (v2_tops_2 @ sk_B @ sk_A)
% 2.87/3.05        | ~ (m1_subset_1 @ sk_B @ 
% 2.87/3.05             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.87/3.05      inference('sup-', [status(thm)], ['44', '51'])).
% 2.87/3.05  thf('53', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('54', plain,
% 2.87/3.05      ((m1_subset_1 @ sk_B @ 
% 2.87/3.05        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.87/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.87/3.05  thf('55', plain,
% 2.87/3.05      ((v2_tops_2 @ 
% 2.87/3.05        (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_C @ sk_B) @ 
% 2.87/3.05        sk_A)),
% 2.87/3.05      inference('demod', [status(thm)], ['52', '53', '54'])).
% 2.87/3.05  thf('56', plain, ($false), inference('demod', [status(thm)], ['4', '55'])).
% 2.87/3.05  
% 2.87/3.05  % SZS output end Refutation
% 2.87/3.05  
% 2.87/3.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
