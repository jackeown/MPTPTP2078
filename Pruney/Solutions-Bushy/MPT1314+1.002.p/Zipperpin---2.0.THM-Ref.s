%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1314+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VNSE4RwkbG

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:28 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 111 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  454 (1152 expanded)
%              Number of equality atoms :   14 (  40 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X2 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X16 @ ( k2_struct_0 @ X13 ) )
       != X15 )
      | ~ ( v3_pre_topc @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X16 @ ( k2_struct_0 @ X13 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X16 @ ( k2_struct_0 @ X13 ) ) @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_B @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_B @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,
    ( ( v3_pre_topc @ ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','26'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('40',plain,(
    v3_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['27','38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['2','40'])).


%------------------------------------------------------------------------------
