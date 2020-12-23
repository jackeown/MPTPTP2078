%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iaYeKC1F2P

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 378 expanded)
%              Number of leaves         :   32 ( 123 expanded)
%              Depth                    :   13
%              Number of atoms          :  728 (4746 expanded)
%              Number of equality atoms :   30 ( 186 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ~ ( v3_pre_topc @ sk_D_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_3 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D_3 = sk_B ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X30 @ ( k2_struct_0 @ X27 ) )
       != X29 )
      | ~ ( v3_pre_topc @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('14',plain,(
    ! [X27: $i,X28: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X30 @ ( k2_struct_0 @ X27 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X30 @ ( k2_struct_0 @ X27 ) ) @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X23 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('19',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( l1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['19','24'])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tarski @ ( k2_struct_0 @ X18 ) @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('29',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X12
       != ( k1_pre_topc @ X11 @ X10 ) )
      | ( ( k2_struct_0 @ X12 )
        = X10 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( v1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X11 @ X10 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X11 @ X10 ) @ X11 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['19','24'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('37',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('39',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('41',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['33','34','39','40'])).

thf('42',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['19','24'])).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( l1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('46',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','41','46'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_B @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','49','50','51','52','53'])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_C_1 )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['2','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iaYeKC1F2P
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 73 iterations in 0.046s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.21/0.48  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.48  thf(t33_tops_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.48               ( ( v3_pre_topc @ B @ A ) =>
% 0.21/0.48                 ( ![D:$i]:
% 0.21/0.48                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.48                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( l1_pre_topc @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48              ( ![C:$i]:
% 0.21/0.48                ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.48                  ( ( v3_pre_topc @ B @ A ) =>
% 0.21/0.48                    ( ![D:$i]:
% 0.21/0.48                      ( ( m1_subset_1 @
% 0.21/0.48                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.48                        ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t33_tops_2])).
% 0.21/0.48  thf('0', plain, (~ (v3_pre_topc @ sk_D_3 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain, (((sk_D_3) = (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('2', plain, (~ (v3_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, (((sk_D_3) = (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf(commutativity_k9_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.48         (((k9_subset_1 @ X4 @ X6 @ X5) = (k9_subset_1 @ X4 @ X5 @ X6))
% 0.21/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.21/0.48           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.21/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.21/0.48           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k3_xboole_0 @ X0 @ sk_B)
% 0.21/0.48           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.48  thf(t32_tops_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.48               ( ( v3_pre_topc @ C @ B ) <=>
% 0.21/0.48                 ( ?[D:$i]:
% 0.21/0.48                   ( ( ( k9_subset_1 @
% 0.21/0.48                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.21/0.48                       ( C ) ) & 
% 0.21/0.48                     ( v3_pre_topc @ D @ A ) & 
% 0.21/0.48                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X27 @ X28)
% 0.21/0.48          | ((k9_subset_1 @ (u1_struct_0 @ X27) @ X30 @ (k2_struct_0 @ X27))
% 0.21/0.48              != (X29))
% 0.21/0.48          | ~ (v3_pre_topc @ X30 @ X28)
% 0.21/0.48          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.48          | (v3_pre_topc @ X29 @ X27)
% 0.21/0.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.48          | ~ (l1_pre_topc @ X28))),
% 0.21/0.48      inference('cnf', [status(esa)], [t32_tops_2])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X27 : $i, X28 : $i, X30 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X28)
% 0.21/0.48          | ~ (m1_subset_1 @ 
% 0.21/0.48               (k9_subset_1 @ (u1_struct_0 @ X27) @ X30 @ (k2_struct_0 @ X27)) @ 
% 0.21/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.48          | (v3_pre_topc @ 
% 0.21/0.48             (k9_subset_1 @ (u1_struct_0 @ X27) @ X30 @ (k2_struct_0 @ X27)) @ 
% 0.21/0.48             X27)
% 0.21/0.48          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.48          | ~ (v3_pre_topc @ X30 @ X28)
% 0.21/0.48          | ~ (m1_pre_topc @ X27 @ X28))),
% 0.21/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ (k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.48          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.48          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.48          | (v3_pre_topc @ 
% 0.21/0.48             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 0.21/0.48              (k2_struct_0 @ sk_C_1)) @ 
% 0.21/0.48             sk_C_1)
% 0.21/0.48          | ~ (l1_pre_topc @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf(dt_k1_pre_topc, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.21/0.48         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X23 : $i, X24 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X23)
% 0.21/0.48          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.48          | (m1_pre_topc @ (k1_pre_topc @ X23 @ X24) @ X23))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_m1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X25 : $i, X26 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X25 @ X26)
% 0.21/0.48          | (l1_pre_topc @ X25)
% 0.21/0.48          | ~ (l1_pre_topc @ X26))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '24'])).
% 0.21/0.48  thf(d9_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( l1_pre_topc @ B ) =>
% 0.21/0.48           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.48             ( ( ![C:$i]:
% 0.21/0.48                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.48                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.48                     ( ?[D:$i]:
% 0.21/0.48                       ( ( m1_subset_1 @
% 0.21/0.48                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.48                         ( ( C ) =
% 0.21/0.48                           ( k9_subset_1 @
% 0.21/0.48                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.21/0.48               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_2, axiom,
% 0.21/0.48    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.48       ( ( ( C ) =
% 0.21/0.48           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.21/0.48         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_3, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( l1_pre_topc @ B ) =>
% 0.21/0.48           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.48             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.21/0.48               ( ![C:$i]:
% 0.21/0.48                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.48                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.48                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X18)
% 0.21/0.48          | ~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.48          | (r1_tarski @ (k2_struct_0 @ X18) @ (k2_struct_0 @ X19))
% 0.21/0.48          | ~ (l1_pre_topc @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.48        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 0.21/0.48           (k2_struct_0 @ sk_C_1))
% 0.21/0.48        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 0.21/0.48         (k2_struct_0 @ sk_C_1))
% 0.21/0.48        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf(d10_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.48               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.21/0.48                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.48          | ((X12) != (k1_pre_topc @ X11 @ X10))
% 0.21/0.48          | ((k2_struct_0 @ X12) = (X10))
% 0.21/0.48          | ~ (m1_pre_topc @ X12 @ X11)
% 0.21/0.48          | ~ (v1_pre_topc @ X12)
% 0.21/0.48          | ~ (l1_pre_topc @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X11)
% 0.21/0.48          | ~ (v1_pre_topc @ (k1_pre_topc @ X11 @ X10))
% 0.21/0.48          | ~ (m1_pre_topc @ (k1_pre_topc @ X11 @ X10) @ X11)
% 0.21/0.48          | ((k2_struct_0 @ (k1_pre_topc @ X11 @ X10)) = (X10))
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 0.21/0.48        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.21/0.48        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['30', '32'])).
% 0.21/0.48  thf('34', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '24'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X23 : $i, X24 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X23)
% 0.21/0.48          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.48          | (v1_pre_topc @ (k1_pre_topc @ X23 @ X24)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 0.21/0.48        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('39', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('41', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['33', '34', '39', '40'])).
% 0.21/0.48  thf('42', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '24'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X25 : $i, X26 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X25 @ X26)
% 0.21/0.48          | (l1_pre_topc @ X25)
% 0.21/0.48          | ~ (l1_pre_topc @ X26))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.48        | (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('46', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_C_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '41', '46'])).
% 0.21/0.48  thf(t28_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.48  thf('49', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k3_xboole_0 @ X0 @ sk_B)
% 0.21/0.48           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.48  thf('53', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.48          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.48          | (v3_pre_topc @ sk_B @ sk_C_1)
% 0.21/0.48          | ~ (l1_pre_topc @ X0))),
% 0.21/0.48      inference('demod', [status(thm)],
% 0.21/0.48                ['15', '16', '49', '50', '51', '52', '53'])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v3_pre_topc @ sk_B @ sk_C_1)
% 0.21/0.48        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.21/0.48        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '54'])).
% 0.21/0.48  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('57', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('58', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('59', plain, ((v3_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.48  thf('60', plain, ($false), inference('demod', [status(thm)], ['2', '59'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
