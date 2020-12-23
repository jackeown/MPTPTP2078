%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mIhHLu8A21

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:34 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 533 expanded)
%              Number of leaves         :   30 ( 166 expanded)
%              Depth                    :   13
%              Number of atoms          :  890 (7684 expanded)
%              Number of equality atoms :   48 ( 402 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t34_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v4_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v4_pre_topc @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                     => ( ( D = B )
                       => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_2])).

thf('0',plain,(
    ~ ( v4_pre_topc @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X14 @ X16 @ X15 )
        = ( k9_subset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k9_subset_1 @ X19 @ X17 @ X18 )
        = ( k3_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t43_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v4_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v4_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X28 @ ( k2_struct_0 @ X25 ) )
       != X27 )
      | ~ ( v4_pre_topc @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v4_pre_topc @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('14',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X28 @ ( k2_struct_0 @ X25 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X28 @ ( k2_struct_0 @ X25 ) ) @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_C ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( C = D )
                   => ( ( k2_pre_topc @ B @ D )
                      = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ ( k2_pre_topc @ A @ C ) @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_pre_topc @ X29 @ X31 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k2_pre_topc @ X30 @ X32 ) @ ( k2_struct_0 @ X29 ) ) )
      | ( X32 != X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_pre_topc])).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_pre_topc @ X29 @ X31 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k2_pre_topc @ X30 @ X31 ) @ ( k2_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_pre_topc @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k2_pre_topc @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k2_pre_topc @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_B @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','30','31'])).

thf('33',plain,
    ( ( ( k2_pre_topc @ sk_C @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_pre_topc @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( k2_pre_topc @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_C @ sk_B ) @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','37','38'])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_C @ sk_B ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ X33 @ ( k2_pre_topc @ X34 @ X33 ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( l1_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,
    ( ( k2_pre_topc @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('63',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['52','61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('65',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['52','61','62'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ sk_B @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['39','63','64','65'])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_C )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v4_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['2','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mIhHLu8A21
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.62  % Solved by: fo/fo7.sh
% 0.45/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.62  % done 335 iterations in 0.162s
% 0.45/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.62  % SZS output start Refutation
% 0.45/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.62  thf(t34_tops_2, conjecture,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( l1_pre_topc @ A ) =>
% 0.45/0.62       ( ![B:$i]:
% 0.45/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.62           ( ![C:$i]:
% 0.45/0.62             ( ( m1_pre_topc @ C @ A ) =>
% 0.45/0.62               ( ( v4_pre_topc @ B @ A ) =>
% 0.45/0.62                 ( ![D:$i]:
% 0.45/0.62                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.45/0.62                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.62    (~( ![A:$i]:
% 0.45/0.62        ( ( l1_pre_topc @ A ) =>
% 0.45/0.62          ( ![B:$i]:
% 0.45/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.62              ( ![C:$i]:
% 0.45/0.62                ( ( m1_pre_topc @ C @ A ) =>
% 0.45/0.62                  ( ( v4_pre_topc @ B @ A ) =>
% 0.45/0.62                    ( ![D:$i]:
% 0.45/0.62                      ( ( m1_subset_1 @
% 0.45/0.62                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.45/0.62                        ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.62    inference('cnf.neg', [status(esa)], [t34_tops_2])).
% 0.45/0.62  thf('0', plain, (~ (v4_pre_topc @ sk_D_1 @ sk_C)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('1', plain, (((sk_D_1) = (sk_B))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('2', plain, (~ (v4_pre_topc @ sk_B @ sk_C)),
% 0.45/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.62  thf('3', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('4', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('5', plain, (((sk_D_1) = (sk_B))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('6', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.62  thf(commutativity_k9_subset_1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.45/0.62  thf('7', plain,
% 0.45/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.62         (((k9_subset_1 @ X14 @ X16 @ X15) = (k9_subset_1 @ X14 @ X15 @ X16))
% 0.45/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.45/0.62      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.45/0.62  thf('8', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_C) @ X0 @ sk_B)
% 0.45/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.62  thf('9', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.62  thf(redefinition_k9_subset_1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.62  thf('10', plain,
% 0.45/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.62         (((k9_subset_1 @ X19 @ X17 @ X18) = (k3_xboole_0 @ X17 @ X18))
% 0.45/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.45/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.45/0.62  thf('11', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_C) @ X0 @ sk_B)
% 0.45/0.62           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.45/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.62  thf('12', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((k3_xboole_0 @ X0 @ sk_B)
% 0.45/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['8', '11'])).
% 0.45/0.62  thf(t43_pre_topc, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( l1_pre_topc @ A ) =>
% 0.45/0.62       ( ![B:$i]:
% 0.45/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.62           ( ![C:$i]:
% 0.45/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.45/0.62               ( ( v4_pre_topc @ C @ B ) <=>
% 0.45/0.62                 ( ?[D:$i]:
% 0.45/0.62                   ( ( ( k9_subset_1 @
% 0.45/0.62                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.45/0.62                       ( C ) ) & 
% 0.45/0.62                     ( v4_pre_topc @ D @ A ) & 
% 0.45/0.62                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.62  thf('13', plain,
% 0.45/0.62      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.62         (~ (m1_pre_topc @ X25 @ X26)
% 0.45/0.62          | ((k9_subset_1 @ (u1_struct_0 @ X25) @ X28 @ (k2_struct_0 @ X25))
% 0.45/0.62              != (X27))
% 0.45/0.62          | ~ (v4_pre_topc @ X28 @ X26)
% 0.45/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.62          | (v4_pre_topc @ X27 @ X25)
% 0.45/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.45/0.62          | ~ (l1_pre_topc @ X26))),
% 0.45/0.62      inference('cnf', [status(esa)], [t43_pre_topc])).
% 0.45/0.62  thf('14', plain,
% 0.45/0.62      (![X25 : $i, X26 : $i, X28 : $i]:
% 0.45/0.62         (~ (l1_pre_topc @ X26)
% 0.45/0.62          | ~ (m1_subset_1 @ 
% 0.45/0.62               (k9_subset_1 @ (u1_struct_0 @ X25) @ X28 @ (k2_struct_0 @ X25)) @ 
% 0.45/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.45/0.62          | (v4_pre_topc @ 
% 0.45/0.62             (k9_subset_1 @ (u1_struct_0 @ X25) @ X28 @ (k2_struct_0 @ X25)) @ 
% 0.45/0.62             X25)
% 0.45/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.62          | ~ (v4_pre_topc @ X28 @ X26)
% 0.45/0.62          | ~ (m1_pre_topc @ X25 @ X26))),
% 0.45/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.45/0.62  thf('15', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (~ (m1_subset_1 @ (k3_xboole_0 @ (k2_struct_0 @ sk_C) @ sk_B) @ 
% 0.45/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.45/0.62          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.45/0.62          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.45/0.62          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.62          | (v4_pre_topc @ 
% 0.45/0.62             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.45/0.62             sk_C)
% 0.45/0.62          | ~ (l1_pre_topc @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['12', '14'])).
% 0.45/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.62  thf('16', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.62  thf('17', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((k3_xboole_0 @ X0 @ sk_B)
% 0.45/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['8', '11'])).
% 0.45/0.62  thf('18', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.62  thf('19', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (~ (m1_subset_1 @ (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.45/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.45/0.62          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.45/0.62          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.45/0.62          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.62          | (v4_pre_topc @ (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) @ sk_C)
% 0.45/0.62          | ~ (l1_pre_topc @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.45/0.62  thf('20', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.62  thf('21', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf(t47_pre_topc, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( l1_pre_topc @ A ) =>
% 0.45/0.62       ( ![B:$i]:
% 0.45/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.62           ( ![C:$i]:
% 0.45/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.62               ( ![D:$i]:
% 0.45/0.62                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.45/0.62                   ( ( ( C ) = ( D ) ) =>
% 0.45/0.62                     ( ( k2_pre_topc @ B @ D ) =
% 0.45/0.62                       ( k9_subset_1 @
% 0.45/0.62                         ( u1_struct_0 @ B ) @ ( k2_pre_topc @ A @ C ) @ 
% 0.45/0.62                         ( k2_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.62  thf('22', plain,
% 0.45/0.62      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.62         (~ (m1_pre_topc @ X29 @ X30)
% 0.45/0.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.45/0.62          | ((k2_pre_topc @ X29 @ X31)
% 0.45/0.62              = (k9_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.45/0.62                 (k2_pre_topc @ X30 @ X32) @ (k2_struct_0 @ X29)))
% 0.45/0.62          | ((X32) != (X31))
% 0.45/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.45/0.62          | ~ (l1_pre_topc @ X30))),
% 0.45/0.62      inference('cnf', [status(esa)], [t47_pre_topc])).
% 0.45/0.62  thf('23', plain,
% 0.45/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.62         (~ (l1_pre_topc @ X30)
% 0.45/0.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.45/0.62          | ((k2_pre_topc @ X29 @ X31)
% 0.45/0.62              = (k9_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.45/0.62                 (k2_pre_topc @ X30 @ X31) @ (k2_struct_0 @ X29)))
% 0.45/0.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.45/0.62          | ~ (m1_pre_topc @ X29 @ X30))),
% 0.45/0.62      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.62  thf('24', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.62          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.62          | ((k2_pre_topc @ X0 @ sk_B)
% 0.45/0.62              = (k9_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.62                 (k2_pre_topc @ sk_A @ sk_B) @ (k2_struct_0 @ X0)))
% 0.45/0.62          | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.62      inference('sup-', [status(thm)], ['21', '23'])).
% 0.45/0.62  thf('25', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf(t52_pre_topc, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( l1_pre_topc @ A ) =>
% 0.45/0.62       ( ![B:$i]:
% 0.45/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.62           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.45/0.62             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.45/0.62               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.45/0.62  thf('26', plain,
% 0.45/0.62      (![X35 : $i, X36 : $i]:
% 0.45/0.62         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.45/0.62          | ~ (v4_pre_topc @ X35 @ X36)
% 0.45/0.62          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 0.45/0.62          | ~ (l1_pre_topc @ X36))),
% 0.45/0.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.45/0.62  thf('27', plain,
% 0.45/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.62        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.45/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.62  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('29', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('30', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.45/0.62      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.45/0.62  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('32', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.62          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.62          | ((k2_pre_topc @ X0 @ sk_B)
% 0.45/0.62              = (k9_subset_1 @ (u1_struct_0 @ X0) @ sk_B @ (k2_struct_0 @ X0))))),
% 0.45/0.62      inference('demod', [status(thm)], ['24', '30', '31'])).
% 0.45/0.62  thf('33', plain,
% 0.45/0.62      ((((k2_pre_topc @ sk_C @ sk_B)
% 0.45/0.62          = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)))
% 0.45/0.62        | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.45/0.62      inference('sup-', [status(thm)], ['20', '32'])).
% 0.45/0.62  thf('34', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((k3_xboole_0 @ X0 @ sk_B)
% 0.45/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['8', '11'])).
% 0.45/0.62  thf('35', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.62  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('37', plain,
% 0.45/0.62      (((k2_pre_topc @ sk_C @ sk_B)
% 0.45/0.62         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.45/0.62  thf('38', plain,
% 0.45/0.62      (((k2_pre_topc @ sk_C @ sk_B)
% 0.45/0.62         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.45/0.62  thf('39', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (~ (m1_subset_1 @ (k2_pre_topc @ sk_C @ sk_B) @ 
% 0.45/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.45/0.62          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.45/0.62          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.45/0.62          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.62          | (v4_pre_topc @ (k2_pre_topc @ sk_C @ sk_B) @ sk_C)
% 0.45/0.62          | ~ (l1_pre_topc @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['19', '37', '38'])).
% 0.45/0.62  thf('40', plain,
% 0.45/0.62      (((k2_pre_topc @ sk_C @ sk_B)
% 0.45/0.62         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.45/0.62  thf('41', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.62  thf(t22_xboole_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.45/0.62  thf('42', plain,
% 0.45/0.62      (![X5 : $i, X6 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 0.45/0.62      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.45/0.62  thf(t31_xboole_1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( r1_tarski @
% 0.45/0.62       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.45/0.62       ( k2_xboole_0 @ B @ C ) ))).
% 0.45/0.62  thf('43', plain,
% 0.45/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.62         (r1_tarski @ 
% 0.45/0.62          (k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k3_xboole_0 @ X11 @ X13)) @ 
% 0.45/0.62          (k2_xboole_0 @ X12 @ X13))),
% 0.45/0.62      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.45/0.62  thf(t23_xboole_1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.45/0.62       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.45/0.62  thf('44', plain,
% 0.45/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.62         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.45/0.62           = (k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.45/0.62  thf('45', plain,
% 0.45/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.62         (r1_tarski @ (k3_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)) @ 
% 0.45/0.62          (k2_xboole_0 @ X12 @ X13))),
% 0.45/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.62  thf('46', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.62         (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ 
% 0.45/0.62          (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.62      inference('sup+', [status(thm)], ['42', '45'])).
% 0.45/0.62  thf('47', plain,
% 0.45/0.62      (![X5 : $i, X6 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 0.45/0.62      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.45/0.62  thf('48', plain,
% 0.45/0.62      (![X0 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X0)),
% 0.45/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.45/0.62  thf('49', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.45/0.62      inference('sup+', [status(thm)], ['41', '48'])).
% 0.45/0.62  thf(d10_xboole_0, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.62  thf('50', plain,
% 0.45/0.62      (![X2 : $i, X4 : $i]:
% 0.45/0.62         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.45/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.62  thf('51', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.62          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.62  thf('52', plain,
% 0.45/0.62      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_C @ sk_B))
% 0.45/0.62        | ((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['40', '51'])).
% 0.45/0.62  thf('53', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.62  thf(t48_pre_topc, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( l1_pre_topc @ A ) =>
% 0.45/0.62       ( ![B:$i]:
% 0.45/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.62           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.45/0.62  thf('54', plain,
% 0.45/0.62      (![X33 : $i, X34 : $i]:
% 0.45/0.62         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.45/0.62          | (r1_tarski @ X33 @ (k2_pre_topc @ X34 @ X33))
% 0.45/0.62          | ~ (l1_pre_topc @ X34))),
% 0.45/0.62      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.45/0.62  thf('55', plain,
% 0.45/0.62      ((~ (l1_pre_topc @ sk_C)
% 0.45/0.62        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_C @ sk_B)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.62  thf('56', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf(dt_m1_pre_topc, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( l1_pre_topc @ A ) =>
% 0.45/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.45/0.62  thf('57', plain,
% 0.45/0.62      (![X20 : $i, X21 : $i]:
% 0.45/0.62         (~ (m1_pre_topc @ X20 @ X21)
% 0.45/0.62          | (l1_pre_topc @ X20)
% 0.45/0.62          | ~ (l1_pre_topc @ X21))),
% 0.45/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.62  thf('58', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.45/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.62  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('60', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.62      inference('demod', [status(thm)], ['58', '59'])).
% 0.45/0.62  thf('61', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_C @ sk_B))),
% 0.45/0.62      inference('demod', [status(thm)], ['55', '60'])).
% 0.45/0.62  thf('62', plain,
% 0.45/0.62      (((k2_pre_topc @ sk_C @ sk_B)
% 0.45/0.62         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.45/0.62  thf('63', plain, (((sk_B) = (k2_pre_topc @ sk_C @ sk_B))),
% 0.45/0.62      inference('demod', [status(thm)], ['52', '61', '62'])).
% 0.45/0.62  thf('64', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.62  thf('65', plain, (((sk_B) = (k2_pre_topc @ sk_C @ sk_B))),
% 0.45/0.62      inference('demod', [status(thm)], ['52', '61', '62'])).
% 0.45/0.62  thf('66', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (~ (m1_pre_topc @ sk_C @ X0)
% 0.45/0.62          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.45/0.62          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.62          | (v4_pre_topc @ sk_B @ sk_C)
% 0.45/0.62          | ~ (l1_pre_topc @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['39', '63', '64', '65'])).
% 0.45/0.62  thf('67', plain,
% 0.45/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.62        | (v4_pre_topc @ sk_B @ sk_C)
% 0.45/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.62        | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.45/0.62      inference('sup-', [status(thm)], ['3', '66'])).
% 0.45/0.62  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('69', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('70', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('71', plain, ((v4_pre_topc @ sk_B @ sk_C)),
% 0.45/0.62      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.45/0.62  thf('72', plain, ($false), inference('demod', [status(thm)], ['2', '71'])).
% 0.45/0.62  
% 0.45/0.62  % SZS output end Refutation
% 0.45/0.62  
% 0.50/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
